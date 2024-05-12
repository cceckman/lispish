use lispish_store::{Error, Ptr, Storage};

mod location;
mod tokens;

pub struct Parser<'a> {
    store: &'a mut Storage,
}

impl<'a> Parser<'a> {
    pub fn new(store: &'a mut Storage) -> Self {
        Parser { store }
    }

    pub fn parse(&mut self, input: impl Iterator<Item = char>) -> Result<(), Error> {
        let st = self.store.put_string(input);
        self.store.push(st);
        todo!()
    }
}

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
