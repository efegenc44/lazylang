#[derive(Clone, Debug)]
pub struct Ranged<T> {
    pub data: T,
    pub col_start: usize,
    pub col_end: usize,
    pub row_start: usize,
    pub row_end: usize,
}

pub type Ranges = ((usize, usize), (usize, usize));

impl<T> Ranged<T> {
    pub const fn new(data: T, ((col_start, row_start), (col_end, row_end)): Ranges) -> Self {
        Self {
            data,
            col_start,
            col_end,
            row_start,
            row_end,
        }
    }

    pub const fn starts(&self) -> (usize, usize) {
        (self.col_start, self.row_start)
    }

    pub const fn ends(&self) -> (usize, usize) {
        (self.col_end, self.row_end)
    }

    pub const fn ranges(&self) -> Ranges {
        (self.starts(), self.ends())
    }

    #[allow(clippy::missing_const_for_fn)]
    // clippy tells this function can be const
    // but rust does not allow
    pub fn into_tuple(self) -> (T, Ranges) {
        let ranges = self.ranges();
        (self.data, ranges)
    }
}
