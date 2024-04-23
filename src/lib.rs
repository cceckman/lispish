//! Basic Lisp parser (and eventually evaluator) at RC.
//!

pub mod reader;

pub mod data;

mod eval;

#[cfg(feature = "web")]
pub mod web;
