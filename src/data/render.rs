use std::collections::{HashMap, VecDeque};

use dot_writer::Attributes;
use dot_writer::DotWriter;

use crate::data::{Object, Pair, Ptr, Storage};

use super::StoredPtr;

fn node_for_ptr(p: Ptr) -> String {
    format!(r#"<{p}>"#)
}

/// Render the state of storage into Graphviz graph.
pub fn render_store<'a>(
    store: &'a Storage,
    labeled_nodes: impl IntoIterator<Item = (StoredPtr, &'a str)>,
) -> Vec<u8> {
    let names: HashMap<_, &'a str> = labeled_nodes.into_iter().collect();
    let mut outbuf = Vec::new();
    {
        let mut writer = DotWriter::from(&mut outbuf);
        let mut graph = writer.digraph();
        let mut queue = VecDeque::new();
        queue.push_back(store.root());

        while let Some(it) = queue.pop_front() {
            if it.is_nil() {
                // We render nil pointers at their source, not their destination.
                continue;
            }

            let id = node_for_ptr(it);
            let mut node = graph.node_named(&id);
            let name = if let Some(label) = names.get(&it.raw) {
                format!("{it}\n{label}")
            } else {
                format!("{it}")
            };

            node.set_shape(dot_writer::Shape::Record);
            match store.get(it) {
                Object::Nil => continue,
                Object::Integer(v) => {
                    node.set_label(&format!("{{{name}|{v}}}"));
                }
                Object::Float(v) => {
                    node.set_label(&format!("{{{name}|{v}}}"));
                }
                Object::String(v) => {
                    let bytes = store.get_string(&v);
                    let v = String::from_utf8_lossy(&bytes);
                    node.set_label(&format!("{{{name}|{v}}}"));
                }
                Object::Symbol(v) => {
                    let v = store.get_symbol(v);
                    node.set_label(&format!("{{{name}|{v}}}"));
                }
                Object::Builtin(fptr) => {
                    node.set_label(&format!("{{{name}|{fptr:p}}}"));
                }
                Object::Pair(Pair { car, cdr }) => {
                    node.set_shape(dot_writer::Shape::None);
                    let car_name = node_for_ptr(car);
                    let cdr_name = node_for_ptr(cdr);
                    let label = format!(
                        "<{}>",
                        maud::html!(
                            table {
                                tr { td colspan="2" border="0" { (name) } }
                                tr {
                                    td port="car" { (car) }
                                    td port="cdr" { (cdr) }
                                }
                            }
                        )
                        .into_string()
                    );
                    node.set_html(&label);
                    let car_port = node.id().port("car");
                    let cdr_port = node.id().port("cdr");
                    std::mem::drop(node);
                    if !car.is_nil() {
                        queue.push_back(car);
                        graph.edge(car_port, car_name);
                    }
                    if !cdr.is_nil() {
                        queue.push_back(cdr);
                        graph.edge(cdr_port, cdr_name);
                    }
                }
            }
        }
    }
    outbuf
}
