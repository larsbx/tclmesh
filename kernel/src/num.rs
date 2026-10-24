//! Canonical decimals: the verified implementation in `tclmesh-kernel-core`
//! (`core/src/decimal.rs`), refining `spec/TclMesh/Decimal.lean`.

use std::cmp::Ordering;
use tclmesh_kernel_core::{decimal, Order};

pub use decimal::Dec as Num;

pub fn parse(text: &str) -> Option<Num> {
    decimal::parse(text.as_bytes())
}

pub fn compare(a: &Num, b: &Num) -> Ordering {
    match decimal::compare(a, b) {
        Order::Lt => Ordering::Less,
        Order::Eq => Ordering::Equal,
        Order::Gt => Ordering::Greater,
    }
}
