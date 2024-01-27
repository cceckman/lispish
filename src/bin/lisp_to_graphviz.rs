//! Render an unevaluated Lisp tree as Graphviz.
//!
//! Inspired by [@thingskatedid][kate] and [Ben Weintraub][ben].
//!
//! [kate]: https://twitter.com/thingskatedid/status/1386077306381242371?ref_src=twsrc%5Etfw
//! [ben]: https://www.benweintraub.com/2022/11/12/graphviz-in-the-terminal/
//!  
//! Usage:
//!
//! ```ignore
//! <input.lisp lisp_to_graphviz | dot -T png >output.png
//! ```

use std::io::{Read, Write};

use lispish::SExpression;

/// Intermediate state when rendering to Graphviz.
struct GraphvizEval {
    node_count: usize,
    output: String,
}

/// Name of a Graphviz node.
struct NodeName(String);

impl GraphvizEval {
    pub fn new() -> Self {
        GraphvizEval {
            node_count: 0,
            output: "digraph { \n".to_owned(),
        }
    }

    pub fn finalize(mut self) -> String {
        self.output += "\n}";
        self.output
    }

    /// Add a node to the graph with the given shape and label.
    /// Returns the node name.
    pub fn add_node(&mut self, shape: &str, label: &str) -> NodeName {
        let id = self.node_count;
        self.node_count += 1;
        let name = format!("mynode_{}", id);
        self.output += &format!("\n  {}[shape={},label=\"{}\"]", name, shape, label);
        NodeName(name)
    }

    /// Add an edge from tail to head.
    pub fn add_edge(&mut self, tail: &NodeName, head: &NodeName) {
        self.output += &format!("\n  {} -> {}", tail.0, head.0);
    }
}

/// Trait that can render to Graphviz.
trait RenderToGraphviz {
    fn render(&self, context: &mut GraphvizEval) -> NodeName;
}

impl RenderToGraphviz for SExpression {
    fn render(&self, context: &mut GraphvizEval) -> NodeName {
        match self {
            SExpression::Atom(atom) => match atom {
                lispish::Atom::Symbol(sym) => context.add_node("diamond", sym.as_str()),
                lispish::Atom::String(string) => {
                    // Double-escape, to go into a "label"
                    let esc1 = string.escaped();
                    let esc2 = esc1.replace(r#"\"#, r#"\\"#).replace('"', r#"\""#);
                    let wrapped = format!(r#"\"{}\""#, esc2);
                    context.add_node("note", &wrapped)
                }
                lispish::Atom::Number(num) => context.add_node("rectangle", &num.to_string()),
            },
            SExpression::List(list) => {
                let node = context.add_node("oval", "()");
                let children: Vec<_> = list.iter().map(|v| v.render(context)).collect();
                for child in children {
                    context.add_edge(&node, &child);
                }
                node
            }
        }
    }
}

fn main() {
    let mut input = std::io::stdin().lock();
    let mut bytes = Vec::new();
    input
        .read_to_end(&mut bytes)
        .expect("error: could not read input");
    let s: String = String::from_utf8(bytes).expect("error: input is not UTF-8");

    let result = lispish::read(&s).expect("error: failed to parse input as Lisp");

    let mut eval = GraphvizEval::new();
    for sexpr in result.into_iter() {
        sexpr.render(&mut eval);
    }
    let graphviz = eval.finalize();

    std::io::stdout()
        .lock()
        .write(graphviz.as_bytes())
        .expect("error: could not write output");
}
