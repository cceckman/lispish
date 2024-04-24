use std::collections::{HashMap, VecDeque};

use dot_writer::Attributes;
use dot_writer::DotWriter;

use crate::data::{Object, Pair, Ptr, Storage};

use super::bitset::BitSet;
use super::StoredPtr;

fn node_for_ptr(p: Ptr) -> String {
    format!(r#"<{p}>"#)
}

/// Render the state of storage into Graphviz graph.
pub fn render_store(store: &Storage, labeled_nodes: &HashMap<StoredPtr, String>) -> Vec<u8> {
    let mut visited_objects = BitSet::new();
    let mut outbuf = Vec::new();
    {
        let mut writer = DotWriter::from(&mut outbuf);
        let mut graph = writer.digraph();
        let mut queue = VecDeque::new();
        queue.push_back(store.root());

        while let Some(it) = queue.pop_front() {
            if visited_objects.get(it.idx()) {
                continue;
            }
            visited_objects.set(it.idx());
            if it.is_nil() {
                // We render nil pointers at their source, not their destination.
                continue;
            }

            let id = node_for_ptr(it);
            let mut node = graph.node_named(&id);

            let obj = store.get(it);
            let (shape, newline) = match obj {
                Object::Pair { .. } => (dot_writer::Shape::None, "<BR/>"),
                _ => (dot_writer::Shape::Record, "\\n"),
            };
            node.set_shape(shape);

            let name = if let Some(label) = labeled_nodes.get(&it.raw) {
                format!("{it}{newline}<B>{label}</B>")
            } else {
                format!("{it}")
            };

            match obj {
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
                    let label = format!(
                        "<{}>",
                        maud::html!(
                            table {
                                tr { td colspan="2" border="0" { (maud::PreEscaped(name)) } }
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

                    for (ptr, port) in [(car, car_port), (cdr, cdr_port)] {
                        if ptr.is_nil() {
                            continue;
                        }
                        // Symbols are addressed by their intern ID, not by an object.
                        // Unique them (so we don't have long edges to the definitions)
                        if ptr.is_symbol() {
                            let v = store.get_symbol_ptr(ptr);
                            let id = {
                                let mut sym_node = graph.node_auto();
                                sym_node.set_shape(dot_writer::Shape::Record);
                                sym_node.set_label(&format!("{{{ptr}|{v}}}"));
                                sym_node.id()
                            };
                            graph.edge(port, id);
                            continue;
                        }
                        let name = node_for_ptr(ptr);
                        graph.edge(port, name);
                        queue.push_back(ptr);
                    }
                }
            }
        }
    }
    outbuf
}
