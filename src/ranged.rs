#[derive(Debug)]
pub struct Ranged<T> {
    pub data: T,
    pub start: usize,
    pub end: usize
}

impl<T> Ranged<T> {
    pub fn new(data: T, start: usize, end: usize) -> Self {
        Self { data, start, end }
    }

    pub fn as_tuple(self) -> (T, usize, usize) {
        (self.data, self.start, self.end)
    }

    pub fn as_ref_tuple(&self) -> (&T, &usize, &usize) {
        (&self.data, &self.start, &self.end)
    }
}


