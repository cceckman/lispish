//! Utility implementations and functions.
//!
//! - Deconstruct a list into a specified number of pointers.

use crate::{Error, Ptr};

impl<'a, const N: usize> TryFrom<Ptr<'a>> for [Ptr<'a>; N] {
    type Error = Error<'a>;

    fn try_from(ptr: Ptr<'a>) -> Result<Self, Self::Error> {
        let mut result = [Ptr::nil(); N];
        result
            .iter_mut()
            .try_fold(ptr, |pair, slot| {
                let pair = pair.get().as_pair()?;
                *slot = pair.car;
                Some(pair.cdr)
            })
            .ok_or(Error::new("not enough entries in list", ptr))?;

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Pair, Storage};

    use super::*;

    #[test]
    fn get_list() {
        let store = Storage::default();
        let head = (1..=3).fold(Ptr::nil(), |cdr, i| {
            let car = store.put(i);
            store.put(Pair::cons(car, cdr))
        });

        let pts: [Ptr; 3] = head.try_into().unwrap();
        let got: Vec<i64> = pts
            .into_iter()
            .map(|v| v.get().as_integer().unwrap())
            .collect();
        assert_eq!(&got, &[3, 2, 1]);
    }
}
