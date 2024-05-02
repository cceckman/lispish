use super::{Error, EvalEnvironment};

impl EvalEnvironment {
    /// Render the eval environment into HTML.
    pub fn render_html(&self) -> Result<maud::PreEscaped<String>, Error> {
        let storage = self.store.render().map_err(Error::Fault)?;
        Ok(maud::html!(
            div class="ops" {
                h3 { "Op Stack" }
                p { (self.completed_ops) " ops complete" }
                table class="stack" {
                    @for op in self.op_stack.iter().rev() {
                        tr { td { (op) } }
                    }
                    tr { td; }
                }
            }
            (storage)
        ))
    }
}
