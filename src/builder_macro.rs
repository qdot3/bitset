/// Creates new bitset with minimum buffer.
///
/// # Example
/// ```
/// use small_bitset::{BitSetU64, bitset};
///
/// let bitset = bitset!(u64, 120);
/// assert_eq!(bitset, BitSetU64::<2>::new(120))
/// ```
#[macro_export]
macro_rules! bitset {
    ( $block:ty, $capacity:expr ) => {
        paste::paste! {
            [<BitSet$block:upper>]::<{ ($capacity as usize).div_ceil(<$block>::BITS as usize) }>::new($capacity)
        }
    };
}

#[cfg(test)]
mod macro_test {
    use crate::{bitset, BitSetU64, BitSetU128};

    #[test]
    fn round_up() {
        let b = bitset!(u64, 100);

        assert_eq!(b, BitSetU64::<2>::new(100));
    }

    #[test]
    fn divisible() {
        let b = bitset!(u128, 200);

        assert_eq!(b, BitSetU128::<2>::new(200))
    }
}
