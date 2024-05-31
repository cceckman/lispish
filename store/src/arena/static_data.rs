use super::{
    static_cell::{self, Handle, StaticCell},
    Bitset, Generation, GenericGenerations,
};

static GEN0: StaticCell<Generation> = StaticCell::new("generation 0");
static GEN1: StaticCell<Generation> = StaticCell::new("generation 1");
static BITSET: StaticCell<Bitset> = StaticCell::new("bitset");

pub type Arenas = GenericGenerations<Handle<'static, Generation>, Handle<'static, Bitset>>;

/// Accessor for a static GenericGenerations object.
pub fn get_arenas() -> Result<Arenas, static_cell::Error> {
    let gen_0 = GEN0.get()?;
    let gen_1 = GEN1.get()?;
    let bitset = BITSET.get()?;
    Ok(GenericGenerations {
        gen_0,
        gen_1,
        bitset,
        generation: 0,
    })
}
