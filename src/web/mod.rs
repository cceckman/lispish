//! Web server for interactive exploration

use crate::eval::{self, Error, EvalEnvironment};
use axum::extract::Path;
use axum::http::header::LOCATION;
use axum::http::StatusCode;
use axum::response::{IntoResponse, Result};
use axum::routing::{get, post};
use axum::Form;
use std::collections::HashMap;
use std::io::Write;
use std::process::Stdio;
use std::sync::Arc;
use std::task::Poll;
use tokio::sync::Mutex;

const STYLE: &[u8] = include_bytes!("style.css");

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

    fn render(&self) -> Result<impl IntoResponse, (StatusCode, String)> {
        let tbcontent = &self.expression;
        let gv = self.state.store().render_gv();
        // TODO: Work out how to make this async.
        let rendered = move || -> Result<String, String> {
            let mut dotgraph = std::process::Command::new("dot")
                .arg("-Tsvg")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .map_err(|e| format!("failed to launch storage render: {e}"))?;
            dotgraph
                .stdin
                .take()
                .unwrap()
                .write_all(&gv)
                .map_err(|e| format!("failed to provide graphviz input: {e}"))?;
            let dotgraph = dotgraph
                .wait_with_output()
                .map_err(|e| format!("failed to complete dot command: {e}"))?;
            if dotgraph.status.success() {
                Ok(String::from_utf8_lossy(&dotgraph.stdout).to_string())
            } else {
                Err(format!(
                    "failed to render stack graph: dot failed: {}",
                    &String::from_utf8_lossy(&dotgraph.stderr)
                ))
            }
        }()
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e))?;

        Ok(maud::html!(
                    DOCTYPE
                    html {
                        head {
                            title { (self.name) }
                            link rel="stylesheet" href="/style.css";
                        }
                        body {
                            main {
                                form method="post" { div class="history" {
                                    @for history in self.history.iter() {
                                    div class="historyline" {
                                        textarea class="expression" disabled { (history.0) }
                                        p class="result" { (history.1) }
                                    }
        }
                                    @if let Some(content) = tbcontent {
                                        textarea class="history latest" disabled { (content) }
                                    } @else {
                                        textarea class="history latest" name="expression" {  }
                                    }
                                    div id="control" {
                                        // input   type="submit"
                                        //         value="Evaluate"
                                        //         method="post"
                                        //         formaction=(format!("/sessions/{}/eval", &self.name));
                                        input   type="submit"
                                                value="Step"
                                                method="post"
                                                formaction=(format!("/sessions/{}/step", &self.name));
                                    }
                                }}
                                div id="store" { (maud::PreEscaped(rendered)) }
                            }
                        }
                    }
            ))
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
    ) -> Result<impl IntoResponse, (StatusCode, String)> {
        let session = sessions.0.session_ptr(&session).await;
        let session = session.lock().await;
        session.render()
    }

    async fn step(
        sessions: axum::extract::State<SessionHandler>,
        Path(session_name): Path<String>,
        Form(form): Form<HashMap<String, String>>,
    ) -> Result<impl IntoResponse, (StatusCode, String)> {
        let session = sessions.0.session_ptr(&session_name).await;
        let mut session = session.lock().await;

        // TODO: Still render, even with an error-status code.
        session
            .step(form.get("expression").map(|s| s.as_str()).unwrap_or(""))
            .map_err(to_http_error)?;

        Ok((
            StatusCode::SEE_OTHER,
            [(LOCATION, format!("/sessions/{session_name}"))],
            "",
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
        .route("/sessions/:session", get(SessionHandler::get))
        .route("/sessions/:session/step", post(SessionHandler::step))
        .with_state(sessions)
}