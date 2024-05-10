use std::collections::{HashMap, VecDeque};

use dot_writer::Attributes;
use dot_writer::DotWriter;
use maud::PreEscaped;
use std::io::Write;
use std::process::Stdio;

use crate::{Object, Pair, Ptr, Storage};

use super::bitset::BitSet;
use super::StorageStats;
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

fn render_vector_element(i: usize, ptr: Ptr) -> PreEscaped<String> {
    maud::html!(tr {
        td { (i) }
        td port=(format!("port{i}")) { (ptr) }
    })
}

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
        maud::html!(tr { td colspan="2" { (v) } })
    }

    let value: maud::PreEscaped<String> = match obj {
        Object::Nil => unreachable!("must not queue to nil pointer"),
        Object::Integer(v) => single_value(v),
        Object::Float(v) => single_value(v),
        Object::Symbol(v) => single_value(store.get_symbol(v)),
        Object::Pair(Pair { car, cdr }) => maud::html!( tr {
                        td port="car" { (car) }
                        td port="cdr" { (cdr) }
        }),
        Object::Bytes(b) => maud::html!(tr {
                        td { (format!("{:x?}", &b[..4])) }
                        td { (format!("{:x?}", &b[4..])) }
        }),
        Object::Vector(v) => maud::html! {
            @for (i, o) in v.enumerate() {
                (render_vector_element(i, o))
            }
        },
    };
    node.set_html(&format!(
        "<{}>",
        maud::html!(
            table {
                (name)
                (value)
            }
        )
        .into_string()
    ));

    let car_port = node.id().port("car");
    let cdr_port = node.id().port("cdr");
    std::mem::drop(node);

    // After completing the node, make the outbound edges.
    let mut result = Vec::new();
    if let Object::Pair(Pair { car, cdr }) = obj {
        for (ptr, port) in [(car, car_port), (cdr, cdr_port)] {
            if ptr.is_nil() {
                continue;
            }
            // We always visit successors, even if we aren't going to render them,
            // so we get an accurate count for stats.
            result.push(ptr);

            if ptr.is_symbol() {
                // Symbols are addressed by their intern ID, not by an object.
                // Generate a unique node for each visit.
                // Unique them (so we don't have long edges to the definitions)
                let (id, _) = render_node(store, object_meta, graph, ptr);
                graph.edge(port, id);
                result.push(ptr);
            } else {
                // Need to render the target node on the next pass.
                let name = node_for_ptr(ptr);
                graph.edge(port, name);
            }
        }
    };
    if let Object::Vector(v) = obj {
        for (i, ptr) in v.enumerate() {
            let port = format!("port{i}");
            if ptr.is_nil() {
                continue;
            }
            // We always visit successors, even if we aren't going to render them,
            // so we get an accurate count for stats.
            result.push(ptr);

            if ptr.is_symbol() {
                // Symbols are addressed by their intern ID, not by an object.
                // Generate a unique node for each visit.
                // Unique them (so we don't have long edges to the definitions)
                let (id, _) = render_node(store, object_meta, graph, ptr);
                graph.edge(port, id);
                result.push(ptr);
            } else {
                // Need to render the target node on the next pass.
                let name = node_for_ptr(ptr);
                graph.edge(port, name);
            }
        }
    }
    (node_id, result)
}

/// Render the state of storage into Graphviz graph.
fn render_gv(store: &Storage, object_meta: &ObjectFormats) -> (StorageStats, Vec<u8>) {
    let mut visited_objects = BitSet::new();
    let mut visited_symbols = BitSet::new();
    let mut stats = StorageStats::default();
    let mut outbuf = Vec::new();
    {
        let mut writer = DotWriter::from(&mut outbuf);
        let mut graph = writer.digraph();
        graph.node_attributes().set_font("monospace");
        let mut queue = VecDeque::new();
        queue.push_back(store.root());

        while let Some(it) = queue.pop_front() {
            // Special-case symbols, since they have their own
            // index space.
            if it.is_symbol() {
                if !visited_symbols.get(it.idx()) {
                    stats.symbols += 1;
                }
                visited_symbols.set(it.idx());
                continue;
            }

            if visited_objects.get(it.idx()) {
                continue;
            }
            visited_objects.set(it.idx());
            if it.is_nil() {
                // We render nil only as a target; we don't insert a node for it.
                continue;
            }
            stats.objects += 1;

            let (_, next) = render_node(store, object_meta, &mut graph, it);
            queue.extend(next);
        }
    }
    (stats, outbuf)
}

impl StorageStats {
    fn render(&self, header: &str) -> maud::PreEscaped<String> {
        maud::html!(
            strong { (header) ": " }
            (self.objects) " objects / "
            (self.symbols) " symbols"
        )
    }
}

impl Storage {
    pub fn render(&self) -> Result<maud::PreEscaped<String>, String> {
        let labels = self.labels.borrow();
        let (render_stats, gv) = render_gv(self, &labels);
        std::mem::drop(labels);
        let stats = self.current_stats();
        let max_stats = self.max_stats();

        // TODO: Work out how to make this async;
        // we shouldn't really be holding on for it.
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

            let save_graph = || {
                let _ = tempfile::NamedTempFile::new()
                    .and_then(|mut f| {
                        f.write_all(&gv)?;
                        let (_, pathbuf) = f.keep()?;
                        Ok(pathbuf)
                    })
                    .map(|pathbuf| {
                        tracing::info!("DOT source in {}", pathbuf.display());
                    });
            };
            if !dotgraph.status.success() || std::env::var_os("LISPISH_SAVE_GRAPH").is_some() {
                save_graph();
            }

            if dotgraph.status.success() {
                Ok(String::from_utf8_lossy(&dotgraph.stdout).to_string())
            } else {
                Err(format!(
                    "failed to render stack graph: dot failed: {}",
                    &String::from_utf8_lossy(&dotgraph.stderr)
                ))
            }
        }()
        .map_err(|e| format!("error in rendering stack: {e}"))?;

        Ok(maud::html!(
                div class="heap" {
                    h3 { "Storage" }
                    p class="storage-stats" {
                        (stats.render("current"))
                        " | "
                        (render_stats.render("traced"))
                        " | "
                        (max_stats.render("peak"))
                    }
                    div class="heap-display" {
                        (maud::PreEscaped(graph_svg))
                    }
                }

        ))
    }
}
