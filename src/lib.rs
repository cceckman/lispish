//! Basic Lisp parser (and eventually evaluator) at RC.
//!

pub mod reader;

pub mod data;

mod eval;
#[cfg(feature = "render")]
mod render;
#[cfg(feature = "render")]
pub use render::render_store;

#[cfg(feature = "web")]
pub mod web;
