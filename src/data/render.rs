use std::collections::{HashMap, VecDeque};

use dot_writer::Attributes;
use dot_writer::DotWriter;

use crate::data::{Object, Pair, Ptr, Storage};

use super::bitset::BitSet;
use super::StoredPtr;

fn node_for_ptr(p: Ptr) -> String {
    format!(r#"<{p}>"#)
}

/// Object metadata, for rendering purposes.
#[derive(Default)]
pub struct ObjectFormat {
    pub label: String,
    pub bg_color: String,
}

pub type ObjectFormats = HashMap<StoredPtr, ObjectFormat>;

fn render_node<'a>(
    store: &'a Storage,
    object_meta: &ObjectFormats,
    graph: &mut dot_writer::Scope,
    it: Ptr<'a>,
) -> (dot_writer::NodeId, Vec<Ptr<'a>>) {
    let id = node_for_ptr(it);
    let mut node = if it.is_symbol() {
        graph.node_auto()
    } else {
        graph.node_named(&id)
    };
    let node_id = node.id();

    let obj = store.get(it);
    node.set_shape(dot_writer::Shape::None);

    let get_name = |ptr: &Ptr| {
        let name = object_meta
            .get(&ptr.raw)
            .map(|m| m.label.as_str())
            .unwrap_or("");
        if name.is_empty() {
            maud::html!(
                tr {
                    td border="0" colspan="2" port="id" { (it) }
                }
            )
        } else {
            maud::html!(
                tr { td border="0" colspan="2" port="id" { (it) }}
                tr { td border="0" colspan="2" port="label" align="text" { b { (name) } }}
            )
        }
    };
    let name = get_name(&it);

    fn single_value(v: impl std::fmt::Display) -> maud::PreEscaped<String> {
        maud::html!(td colspan="2" { (v) })
    }

    let value: maud::PreEscaped<String> = match obj {
        Object::Nil => unreachable!("must not queue to nil pointer"),
        Object::Integer(v) => single_value(v),
        Object::Float(v) => single_value(v),
        Object::String(v) => {
            let bytes = store.get_string(&v);
            single_value(String::from_utf8_lossy(&bytes))
        }
        Object::Symbol(v) => single_value(store.get_symbol(v)),
        Object::Builtin(fptr) => single_value(format!("{fptr:p}")),
        Object::Pair(Pair { car, cdr }) | Object::Function(Pair { car, cdr }) => maud::html!(
                    td port="car" { (car) }
                    td port="cdr" { (cdr) }
        ),
    };
    node.set_html(&format!(
        "<{}>",
        maud::html!(
            table {
                (name)
                tr { (value) }
            }
        )
        .into_string()
    ));

    let car_port = node.id().port("car");
    let cdr_port = node.id().port("cdr");
    std::mem::drop(node);

    // After completing the node, make the outbound edges.
    let mut result = Vec::new();
    if let Object::Pair(Pair { car, cdr }) | Object::Function(Pair { car, cdr }) = obj {
        for (ptr, port) in [(car, car_port), (cdr, cdr_port)] {
            // Symbols are addressed by their intern ID, not by an object.
            // Unique them (so we don't have long edges to the definitions)
            if ptr.is_symbol() {
                // We don't need to track the recursive version here-
                // we know this is a symbol, it won't recurse.
                let (id, _) = render_node(store, object_meta, graph, ptr);
                graph.edge(port, id);
                continue;
            } else if !ptr.is_nil() {
                // Need to render the target node on the next pass.
                let name = node_for_ptr(ptr);
                graph.edge(port, name);
                result.push(ptr);
            }
        }
    };
    (node_id, result)
}

/// Render the state of storage into Graphviz graph.
pub fn render_store(store: &Storage, object_meta: &ObjectFormats) -> Vec<u8> {
    let mut visited_objects = BitSet::new();
    let mut outbuf = Vec::new();
    {
        let mut writer = DotWriter::from(&mut outbuf);
        let mut graph = writer.digraph();
        graph.node_attributes().set_font("monospace");
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
            let (_, next) = render_node(store, object_meta, &mut graph, it);
            queue.extend(next);
        }
    }
    outbuf
}
