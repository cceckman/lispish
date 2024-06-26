//! Web server for interactive exploration

use crate::eval::{self, Error, EvalEnvironment};
use axum::extract::Path;
use axum::http::header::LOCATION;
use axum::http::StatusCode;
use axum::response::{IntoResponse, Result};
use axum::routing::{get, post};
use axum::Form;
use std::collections::HashMap;
use std::sync::Arc;
use std::task::Poll;
use tokio::sync::Mutex;

const STYLE: &[u8] = include_bytes!("style.css");
const APP: &[u8] = include_bytes!("app.js");

struct Session {
    name: String,

    history: Vec<(String, String)>,

    expression: Option<String>,

    /// Persistent environment for the session.
    /// Always contains the last result.
    state: EvalEnvironment,
}

fn to_http_error(err: eval::Error) -> (StatusCode, String) {
    match err {
        Error::UserError(msg) => (StatusCode::BAD_REQUEST, format!("invalid input: {msg}")),
        Error::Fault(msg) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("server error: {msg}"),
        ),
    }
}

impl Session {
    fn new(name: String) -> Self {
        Session {
            name,
            history: Vec::new(),
            state: EvalEnvironment::new(),
            expression: None,
        }
    }

    fn eval(&mut self, expression: &str) -> Result<(), eval::Error> {
        if let Some(current) = self.expression.take() {
            // We're evaluating an expression. Evaluate it to completion.
            match self.state.eval() {
                Err(e) => {
                    self.history.push((current, format!("{e}")));
                    Err(e)
                }
                Ok(_) => {
                    // Retrieve the value.
                    let result = self.state.result()?;
                    self.history
                        .push((current, self.state.store().display(result)));
                    Ok(())
                }
            }
        } else {
            // Start a new expression.
            self.state.start(expression)?;
            // Only "commit" to this expression if it parsed OK.
            self.expression = Some(expression.to_owned());
            // Return after setup (parsing) - we want to give a chance to render before any
            // execution takes place.

            Ok(())
        }
    }

    fn step(&mut self, expression: &str) -> Result<(), eval::Error> {
        if let Some(current) = self.expression.take() {
            // We're evaluating an expression. Single-step.
            match self.state.step() {
                Err(e) => {
                    self.history.push((current, format!("{e}")));
                    Err(e)
                }
                Ok(Poll::Pending) => {
                    self.expression = Some(current);
                    Ok(())
                }
                Ok(Poll::Ready(_)) => {
                    // Retrieve the value.
                    let result = self.state.result()?;
                    self.history
                        .push((current, self.state.store().display(result)));
                    Ok(())
                }
            }
        } else {
            // Start a new expression.
            self.state.start(expression)?;
            // Only "commit" to this expression if it parsed OK.
            self.expression = Some(expression.to_owned());
            // Return after setup (parsing) - we want to give a chance to render before any
            // execution takes place.

            Ok(())
        }
    }

    fn render(&self) -> Result<maud::PreEscaped<String>, (StatusCode, String)> {
        let tbcontent = &self.expression;
        let state = self.state.render_html().map_err(to_http_error)?;

        Ok(maud::html!(
                DOCTYPE
                html {
                    head {
                        title { (self.name) }
                        link rel="stylesheet" href="/style.css";
                        script type="text/javascript" src="/app.js" defer { };
                    }
                    body {
                        main {
                            div id="io" {
                                h3 { "Expressions" }
                                form method="post" {
                                    table class="history" {
                                        @for history in self.history.iter() {
                                            tr class="historyline" {
                                                td { textarea class="expression" disabled { (history.0) } }
                                                td class="result" { (history.1) }
                                            }
                                        }
                                        tr { td {
                                            @if let Some(content) = tbcontent {
                                                textarea class="expression latest" disabled { (content) }
                                            } @else {
                                                textarea class="expression latest" name="expression" {  }
                                            }
                                            } td class="expression";
                                        }
                                    }
                                    div id="control" {
                                        input   type="submit"
                                                value="Evaluate"
                                                method="post"
                                                formaction=(format!("/sessions/{}/eval", &self.name));
                                        input   type="submit"
                                                value="Step"
                                                method="post"
                                                formaction=(format!("/sessions/{}/step", &self.name));
                                        input   type="submit"
                                                value="GC"
                                                method="post"
                                                formaction=(format!("/sessions/{}/gc", &self.name));
                                    }
                                }
                            }
                            (state)
                            dialog id="object-label" popover="auto" {
                                form method="post" {
                                    p { "Object label: " }
                                    input   type="text" name="label" id="popup_label" placeholder="Label" autocomplete="off";
                                    input   type="hidden" name="object_id" id="popup_object_id" value="";
                                    input   type="submit" method="post" value="Set" formaction=(format!("/sessions/{}/format", &self.name));
                                }
                            }
                        }
                    }
                }
        ))
    }

    fn format(&self, object_id: &str, label: &str) -> Result<(), eval::Error> {
        self.state.label(object_id, label)
    }

    fn gc(&mut self) {
        self.state.gc();
    }
}

#[derive(Default, Clone)]
struct SessionHandler {
    sessions: Arc<Mutex<HashMap<String, SessionPtr>>>,
}

type SessionPtr = Arc<Mutex<Session>>;

impl SessionHandler {
    async fn session_ptr(&self, name: &str) -> SessionPtr {
        let mut sessions = self.sessions.lock().await;
        sessions
            .entry(name.to_string())
            .or_insert_with(|| Arc::new(Mutex::new(Session::new(name.to_string()))))
            .clone()
    }

    async fn get(
        sessions: axum::extract::State<SessionHandler>,
        Path(session): Path<String>,
    ) -> Result<impl IntoResponse, impl IntoResponse> {
        let session = sessions.0.session_ptr(&session).await;
        let session = session.lock().await;
        session.render()
    }

    async fn step(
        sessions: axum::extract::State<SessionHandler>,
        Path(session_name): Path<String>,
        Form(form): Form<HashMap<String, String>>,
    ) -> Result<impl IntoResponse, axum::http::Response<axum::body::Body>> {
        let session = sessions.0.session_ptr(&session_name).await;
        let mut session = session.lock().await;

        // We always return "OK" and redirect-
        // even a system error gets displayed next time around.

        // TODO: log fault-type errors.
        if let Err(e) = session.step(form.get("expression").map(|e| e.as_str()).unwrap_or("")) {
            tracing::error!(
                "encountered error in stepping: session: {} error: {}",
                session_name,
                e
            );
        }

        Ok((
            StatusCode::SEE_OTHER,
            [(LOCATION, format!("/sessions/{session_name}"))],
        ))
    }

    async fn eval(
        sessions: axum::extract::State<SessionHandler>,
        Path(session_name): Path<String>,
        Form(form): Form<HashMap<String, String>>,
    ) -> Result<impl IntoResponse, axum::http::Response<axum::body::Body>> {
        let session = sessions.0.session_ptr(&session_name).await;
        let mut session = session.lock().await;

        // We always return "OK" and redirect-
        // even a system error gets displayed next time around.

        // TODO: log fault-type errors.
        if let Err(e) = session.eval(form.get("expression").map(|e| e.as_str()).unwrap_or("")) {
            tracing::error!(
                "encountered error in stepping: session: {} error: {}",
                session_name,
                e
            );
        }

        Ok((
            StatusCode::SEE_OTHER,
            [(LOCATION, format!("/sessions/{session_name}"))],
        ))
    }

    async fn format(
        sessions: axum::extract::State<SessionHandler>,
        Path(session_name): Path<String>,
        Form(form): Form<HashMap<String, String>>,
    ) -> Result<impl IntoResponse, axum::http::Response<axum::body::Body>> {
        let session = sessions.0.session_ptr(&session_name).await;
        let session = session.lock().await;

        let label: &str = form.get("label").map(String::as_str).unwrap_or("");
        let object_id: &str = form.get("object_id").map(String::as_str).unwrap_or("");
        // TODO: Color as well.

        if let Err(e) = session.format(object_id, label) {
            tracing::error!(
                "encountered error in stepping: session: {} error: {}",
                session_name,
                e
            );
        }

        Ok((
            StatusCode::SEE_OTHER,
            [(LOCATION, format!("/sessions/{session_name}"))],
        ))
    }
    async fn gc(
        sessions: axum::extract::State<SessionHandler>,
        Path(session_name): Path<String>,
        Form(_): Form<HashMap<String, String>>,
    ) -> Result<impl IntoResponse, axum::http::Response<axum::body::Body>> {
        let session = sessions.0.session_ptr(&session_name).await;
        let mut session = session.lock().await;
        session.gc();

        Ok((
            StatusCode::SEE_OTHER,
            [(LOCATION, format!("/sessions/{session_name}"))],
        ))
    }
}

pub fn get_server() -> axum::Router {
    let sessions: SessionHandler = Default::default();

    axum::Router::new()
        .route(
            "/",
            get(axum::response::Redirect::temporary("/sessions/singleton")),
        )
        .route(
            "/style.css",
            get(|| async { ([(axum::http::header::CONTENT_TYPE, "text/css")], STYLE) }),
        )
        .route(
            "/app.js",
            get(|| async { ([(axum::http::header::CONTENT_TYPE, "text/javascript")], APP) }),
        )
        .route("/sessions/:session", get(SessionHandler::get))
        .route("/sessions/:session/", get(SessionHandler::get))
        .route("/sessions/:session/step", post(SessionHandler::step))
        .route("/sessions/:session/eval", post(SessionHandler::eval))
        .route("/sessions/:session/format", post(SessionHandler::format))
        .route("/sessions/:session/gc", post(SessionHandler::gc))
        .with_state(sessions)
}
