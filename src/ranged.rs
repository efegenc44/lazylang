#[derive(Clone, Debug)]
pub struct Ranged<T> {
    pub data: T,
    pub start: usize,
    pub end: usize,
}

impl<T> Ranged<T> {
    pub const fn new(data: T, start: usize, end: usize) -> Self {
        Self { data, start, end }
    }

    #[allow(clippy::missing_const_for_fn)]
    // clippy tells this function can be const
    // but rust does not allow
    pub fn into_tuple(self) -> (T, usize, usize) {
        (self.data, self.start, self.end)
    }

    pub const fn as_tuple(&self) -> (&T, &usize, &usize) {
        (&self.data, &self.start, &self.end)
    }
}
