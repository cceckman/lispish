//! Web server for interactive exploration

use crate::data::Storage;
use crate::eval::create_env_stack;
use crate::render_store;
use axum::extract::Path;
use axum::http::StatusCode;
use axum::response::{IntoResponse, Result};
use axum::routing::get;
use std::collections::HashMap;
use std::io::Write;
use std::process::Stdio;
use std::sync::Arc;
use std::time::Instant;
use tokio::sync::Mutex;

const STYLE: &[u8] = include_bytes!("style.css");

struct Session {
    name: String,

    /// Last active time of this session.
    /// Sessions are eventually discarded.
    last_active: Instant,

    history: Vec<String>,

    /// State of the session.
    state: State,
}

enum State {
    /// Not currently evaluating an expression.
    /// The storage pointer reflects the top-level environment.
    Idle(Storage),
    Eval {
        store: Storage,
        expression: String,
    },
}

impl Session {
    fn new(name: String) -> Self {
        let store = Storage::default();
        store.set_root(create_env_stack(&store));
        Session {
            name,
            history: Vec::new(),
            last_active: Instant::now(),
            state: State::Idle(store),
        }
    }

    fn render(&self) -> Result<impl IntoResponse, (StatusCode, String)> {
        let (store, tbcontent) = match &self.state {
            State::Idle(store) => (store, None),
            State::Eval { store, .. } => (store, self.history.last()),
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
                            div id="history" {
                                textarea class="history latest" disabled=(tbcontent.is_some()) { @if let Some(tb) = tbcontent { (tb) } }
                                @for history in self.history.iter() {
                                    textarea class="history" disabled="true" { (history) }
                                }
                            }
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
    async fn get(
        sessions: axum::extract::State<SessionHandler>,
        Path(session): Path<String>,
    ) -> Result<impl IntoResponse, (StatusCode, String)> {
        let mut sessions = sessions.0.sessions.lock().await;
        let session_ptr = sessions
            .entry(session.clone())
            .or_insert_with(|| Arc::new(Mutex::new(Session::new(session))));
        // We have an arc, wait until we're the only thread working on this session.
        let session = session_ptr.lock().await;
        session.render()
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
        .with_state(sessions)
}
