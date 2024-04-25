use super::{Error, EvalEnvironment};

use std::io::Write;
use std::process::Stdio;

impl EvalEnvironment {
    /// Render the eval environment into HTML.
    pub fn render_html(&self) -> Result<maud::PreEscaped<String>, Error> {
        let gv = self.store.render_gv();
        // TODO: Work out how to make this async.
        let graph_svg = move || -> Result<String, String> {
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
        .map_err(|e| Error::Fault(format!("error in rendering stack: {e}")))?;

        Ok(maud::html!(
            div class="eval" {
                div {
                h3 { "Op Stack" }
                table class="stack" {
                    @for op in self.op_stack.iter().rev() {
                        tr { td { (op) } }
                    }
                    tr { td; }
                }}
                div class="heap" {
                    h3 { "Storage" }
                    (maud::PreEscaped(graph_svg))
                }
            }
        ))
    }
}
