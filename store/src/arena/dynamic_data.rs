use super::{Bitset, Generation, GenericGenerations, Init};
use core::convert::Infallible;
use std::alloc::{alloc, Layout};
use std::mem::MaybeUninit;

pub type Arenas = GenericGenerations<Box<Generation>, Box<Bitset>>;

impl Generation {
    /// Perform an in-place boxed allocation of a Generation.
    fn new_boxed() -> Box<Self> {
        // Alas, requires unsafe: https://github.com/rust-lang/rust/issues/53827#issuecomment-572476302
        let layout = Layout::new::<MaybeUninit<Generation>>();
        unsafe {
            let ptr = &mut *(alloc(layout) as *mut MaybeUninit<Generation>);
            let ptr = Generation::init(ptr);
            Box::from_raw(ptr)
        }
    }
}

/// Accessor to create a dynamic GenericGenerations object..
pub fn get_arenas() -> Result<Arenas, Infallible> {
    Ok(GenericGenerations {
        gen_0: Generation::new_boxed(),
        gen_1: Generation::new_boxed(),
        bitset: Box::<Bitset>::default(),
        generation: 0,
    })
}
