//! Web server for interactive exploration

use crate::data::Storage;
use crate::eval::{self, initialize, Error, EvalEnvironment};
use crate::render_store;
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
use std::time::Instant;
use tokio::sync::Mutex;

const STYLE: &[u8] = include_bytes!("style.css");

struct Session {
    name: String,

    /// Last active time of this session.
    /// Sessions are eventually discarded.
    last_active: Instant,

    history: Vec<(String, String)>,

    output: String,

    /// State of the session.
    state: State,
}

enum State {
    /// Not currently evaluating an expression.
    /// The storage pointer reflects the top-level environment.
    Idle(Storage),
    Eval(EvalEnvironment),
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
        let store = Storage::default();
        initialize(&store);
        Session {
            name,
            history: Vec::new(),
            last_active: Instant::now(),
            state: State::Idle(store),
            output: String::new(),
        }
    }

    /// Transition to "evaluating" state if not already there.
    fn start_eval(&mut self, expression: &str) -> Result<(), eval::Error> {
        let store = if let State::Idle(store) = &mut self.state {
            std::mem::take(store)
        } else {
            return Ok(());
        };
        self.history.push((expression.to_owned(), "??".to_owned()));
        match EvalEnvironment::start(store, expression) {
            Err((store, error)) => {
                self.state = State::Idle(store);
                Err(error)
            }
            Ok(eval) => {
                self.state = State::Eval(eval);
                Ok(())
            }
        }
    }

    fn eval(&mut self, expression: &str) -> Result<(), (StatusCode, String)> {
        if expression.is_empty() {
            return Ok(());
        }
        self.start_eval(expression).map_err(to_http_error)?;

        let printable_result = loop {
            if let State::Eval(ref mut ctx) = self.state {
                let result = ctx.step().map_err(to_http_error)?;
                match result {
                    Poll::Pending => continue,
                    Poll::Ready(p) => break ctx.store().display(p),
                }
            } else {
                // TODO: Fix this, we "know" we're in the right state at this point.
                return Err(to_http_error(eval::Error::Fault(
                    "state was not ready-for-eval".to_string(),
                )));
            }
        };

        // We've gotten a result from evaluation.
        // Update state.
        let result: Result<(), eval::Error>;
        (self.state, result) = match self.state {
            State::Eval(ctx) => match ctx.idle() {
                Ok(store) => (State::Idle(store), Ok(())),
                Err((ctx, err)) => (State::Eval(ctx), Err(err)),
            },
            State::Idle(store) => (State::Idle(store), Ok(())),
        };
        result.map_err(to_http_error)?;
        // TODO: Should always be true...
        if let Some((expression, _)) = self.history.pop() {
            self.history.push((expression, printable_result))
        }

        Ok(())
    }

    fn render(&self) -> Result<impl IntoResponse, (StatusCode, String)> {
        let (store, tbcontent) = match &self.state {
            State::Idle(store) => (store, None),
            State::Eval(env) => (env.store(), self.history.last()),
        };
        let gv = render_store(store, []);
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
                                        textarea class="history latest" disabled { (content.0) }
                                    } @else {
                                        textarea class="history latest" name="expression" {  }
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

    async fn eval(
        sessions: axum::extract::State<SessionHandler>,
        Path(session_name): Path<String>,
        Form(form): Form<HashMap<String, String>>,
    ) -> Result<impl IntoResponse, (StatusCode, String)> {
        let session = sessions.0.session_ptr(&session_name).await;
        let mut session = session.lock().await;

        if let Some(expression) = form.get("expression") {
            session.eval(expression)?;
        }

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
        .route("/sessions/:session/eval", post(SessionHandler::eval))
        .with_state(sessions)
}
