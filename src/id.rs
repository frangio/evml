use std::num::NonZeroUsize;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Id(NonZeroUsize);

#[cfg_attr(test, derive(Clone))]
pub struct IdGen(NonZeroUsize);

impl IdGen {
    pub fn new() -> IdGen {
        IdGen(NonZeroUsize::MIN)
    }

    pub fn generate(&mut self) -> Id {
        let id = Id(self.0);
        self.0 = self.0.checked_add(1).expect("integer overflow");
        id
    }
}

#[cfg(test)]
macro_rules! generate_ids {
    ($($id:ident),+ in $ids:ident) => {
        $(let $id = $ids.generate();)+
    };
}

#[cfg(test)]
pub(crate) use generate_ids;
