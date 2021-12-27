/// A simple ring buffer.
#[derive(Clone, Debug, PartialEq)]
pub struct RingBuffer<T, const BUFFER_SIZE: usize>
where
    T: Copy + Default,
{
    elements: [T; BUFFER_SIZE],
}

#[allow(dead_code)]
impl<T, const BUFFER_SIZE: usize> RingBuffer<T, BUFFER_SIZE>
where
    T: Copy + Default + PartialEq,
{
    /// Returns the item at the given index.
    pub fn get(&self, idx: usize) -> T {
        self.elements[Self::transform_idx(idx)]
    }

    /// Returns a mutable reference to the given item.
    pub fn get_mut(&mut self, idx: usize) -> &mut T {
        &mut self.elements[Self::transform_idx(idx)]
    }

    /// Inserts an item into the ring buffer.
    pub fn insert(&mut self, idx: usize, value: T) {
        self.elements[Self::transform_idx(idx)] = value;
    }

    /// Returns a new ring buffer.
    pub fn new() -> Self {
        Self {
            elements: [T::default(); BUFFER_SIZE],
        }
    }

    /// Wraps the given index
    fn transform_idx(idx: usize) -> usize {
        idx % BUFFER_SIZE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SIZE: usize = 1222;
    type Buff = RingBuffer<u8, SIZE>;

    describe!(get => {
        #[test]
        fn under_buffer_size_returns_item(){
            let idx = 55;
            let mut buff = Buff::new();
            buff.insert(idx, 4);
            assert_eq!(buff.elements[idx], buff.get(idx));
        }

        #[test]
        fn over_buffer_size_wraps(){
            let idx = 55;
            let mut buff = Buff::new();
            buff.insert(idx, 4);
            assert_eq!(buff.elements[idx], buff.get(idx + SIZE));
        }
    });

    describe!(get_mut => {
        #[test]
        fn under_buffer_size_returns_item(){
            let idx = 55;
            let mut buff = Buff::new();
            buff.insert(idx, 4);

            *buff.get_mut(idx) = 2;

            assert_eq!(2, buff.get(idx));
        }

        #[test]
        fn over_buffer_size_wraps(){
            let idx = 55;
            let mut buff = Buff::new();
            buff.insert(idx, 4);

            *buff.get_mut(idx + SIZE) = 2;

            assert_eq!(2, buff.get(idx));
        }
    });

    describe!(insert => {
        #[test]
        fn should_overwrite(){
            let mut buff = Buff::new();
            buff.insert(3, 4);
            assert_eq!(4, buff.elements[3]);
        }

        #[test]
        fn should_wrap_indexes(){
            let mut buff = Buff::new();
            let idx = SIZE + 33;
            buff.insert(idx, 4);
            assert_eq!(4, buff.elements[33]);
        }
    });

    describe!(new => {
        #[test]
        fn returns_expected() {
            let expected = RingBuffer {
                elements: [0; SIZE],
            };

            let actual = Buff::new();
            assert_eq!(expected, actual);
        }
    });

    describe!(transform_idx => {
        #[test]
        fn under_buffer_size_returns_idx(){
            let idx = 333;
            assert_eq!(idx, Buff::transform_idx(idx));
        }

          #[test]
        fn over_buffer_size_wraps(){
            let idx = SIZE + 333;
            assert_eq!(333, Buff::transform_idx(idx));
        }
    });
}
