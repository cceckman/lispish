//! Location support.

use lispish_store::{Error, Pair, Ptr, Storage};

// Location in an input stream.
pub struct LazyLocation<'a> {
    pub offset: i64,
    pub name: Ptr<'a>,
    pub content: Ptr<'a>,
}

impl<'a> TryFrom<Ptr<'a>> for LazyLocation<'a> {
    type Error = Error<'a>;
    fn try_from(ptr: Ptr<'a>) -> Result<Self, Self::Error> {
        let [offset, name, content]: [Ptr; 3] = ptr
            .try_into()
            .map_err(|_| Error::new("not enough elements for LazyLocation", ptr))?;
        let offset = offset
            .get()
            .as_integer()
            .ok_or(Error::new("LazyLocation offset is not an integer", ptr))?;

        Ok(LazyLocation {
            offset,
            name,
            content,
        })
    }
}

impl<'a> LazyLocation<'a> {
    pub fn store(&self, store: &'a Storage) -> Ptr<'a> {
        let offset = store.put(self.offset);
        [self.content, self.name, offset]
            .iter()
            .fold(Ptr::nil(), |cdr, &car| store.put(Pair { car, cdr }))
    }
}

#[cfg(test)]
mod tests {
    use lispish_store::{strings::LispString, Storage};

    use super::LazyLocation;

    #[test]
    fn store_and_retrieve() {
        let mut store = Storage::default();
        let name = store.put_string("input cell 1".chars());
        let content = store.put_string("(echo hi)".chars());

        let ptr = {
            let location = LazyLocation {
                offset: 1,
                name,
                content,
            };
            location.store(&store)
        };
        store.push(ptr);
        store.gc();
        let loc: LazyLocation = store.pop().try_into().unwrap();
        assert_eq!(loc.offset, 1);
        let name: LispString = loc.name.try_into().unwrap();
        let name: String = name.into_iter().collect();
        let content: LispString = loc.content.try_into().unwrap();
        let content: String = content.into_iter().collect();

        assert_eq!(&name, "input cell 1");
        assert_eq!(&content, "(echo hi)");
    }
}
