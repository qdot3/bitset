use paste::paste;
use std::ops::Range;

macro_rules! bitset_impl {
    ( $($block:ty)+ ) => {$(
        paste! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub struct [<BitSet$block:upper>]<const N: usize> {
                buffer: [$block; N],
                size: usize,

                count_ones: u32,
            }

            impl <const N: usize> [<BitSet$block:upper>]<N> {
                const B: usize = <$block>::BITS as usize;

                /// Creates a new inline `BitSet`.
                ///
                /// # Panics
                /// Panics
                /// (1) if the stack is overflowed or
                /// (2) if `buffer` is too small (i.e. NB < `size`, where B is the size of `Block`).
                #[inline]
                #[must_use]
                pub fn new(size: usize) -> Self {
                    assert!(
                        size <= N * Self::B,
                        "shortage of buffer: `N` must be {} or more.",
                        size.div_ceil(Self::B)
                    );

                    Self { buffer: [0; N], size , count_ones: 0, }
                }

                #[inline]
                pub const fn len(&self) -> usize {
                    self.size
                }

                #[inline]
                const fn inner_index(&self, i: usize) -> (usize, usize) {
                    (i / Self::B, i % Self::B)
                }

                // Do something with `f` within `range`.
                #[inline]
                fn range_with(&self, range: Range<usize>, mut f: impl FnMut($block) -> ()) {
                    assert!(
                        range.end <= self.size,
                        "index out of bounds: the len is {} but the end of range is {}",
                        self.size, range.end
                    );

                    let Range { start, end } = range;

                    let (is, js) = self.inner_index(start);
                    {
                        let mask = ((!0) >> js) << js;
                        f(self.buffer[is] & mask)
                    }

                    let (ie, je) = self.inner_index(end);
                    if je > 0 {
                        let mask = (!0) >> (Self::B - je);
                        f(self.buffer[ie] & mask)
                    }

                    for i in is + 1..ie {
                        f(self.buffer[i])
                    }
                }

                // Modifies (sub-)blocks with `f` within `range`.
                #[inline]
                fn range_mut_with(&mut self, range: Range<usize>, f: impl Fn($block) -> $block) {
                    assert!(
                        range.end <= self.size,
                        "index out of bounds: the len is {} but the end of range is {}",
                        self.size, range.end
                    );

                    let Range { start, end } = range;

                    let (is, js) = self.inner_index(start);
                    if let Some(block) = self.buffer.get_mut(is) {
                        let mask = ((!0) >> js) << js;
                        let sub_block = *block & mask;

                        *block -= sub_block;
                        self.count_ones -= sub_block.count_ones();

                        let sub_block = f(sub_block) & mask;

                        *block += sub_block;
                        self.count_ones += sub_block.count_ones();
                    }

                    let (ie, je) = self.inner_index(end);
                    if je > 0 {
                        if let Some(block) = self.buffer.get_mut(ie) {
                            let mask = (!0) >> (Self::B - je);
                            let sub_block = *block & mask;

                            *block -= sub_block;
                            self.count_ones -= sub_block.count_ones();

                            let sub_block = f(sub_block) & mask;

                            *block += sub_block;
                            self.count_ones += sub_block.count_ones();
                        }
                    }

                    for i in is + 1..ie {
                        if let Some(block) = self.buffer.get_mut(i) {
                            self.count_ones -= (*block).count_ones();
                            *block = f(*block);
                            self.count_ones += (*block).count_ones();
                        }
                    }
                }

                /// Set `i`-th bit to `1`.
                ///
                /// # Panics
                /// Panics if 'i' is out of bounds.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub fn turn_on(&mut self, i: usize) -> bool {
                    assert!(
                        i < self.size,
                        "index out of bounds: the len is {} but the index is {}",
                        self.size, i
                    );

                    if self.is_on(i) {
                        false
                    } else {
                        self.count_ones += 1;

                        let (i, j) = self.inner_index(i);
                        self.buffer[i] += 1 << j;

                        true
                    }
                }

                /// Set bits in the `range` to `1`.
                ///
                /// # Example
                /// ```
                /// use small_bitset::*;
                ///
                /// let mut bitset = bitset!(u64, 300);
                ///
                /// assert_eq!(bitset.count_ones(), 0);
                /// bitset.turn_on_range(0..300);
                /// assert_eq!(bitset.count_ones(), 300);
                /// ```
                ///
                /// # Panics
                /// Panics if `range `is out of bounds.
                ///
                /// # Time Complexity
                /// O(R/B), where R is size of `range` and B is the size of `Block` (e.g. 64 for u64).
                #[inline]
                pub fn turn_on_range(&mut self, range: Range<usize>) {
                    self.range_mut_with(range, |_| !0);
                }

                /// Set `i`-th bit to `0`.
                ///
                /// # Panics
                /// Panics if `i` is out of bounds.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub fn turn_off(&mut self, i: usize) -> bool {
                    assert!(
                        i < self.size,
                        "index out of bounds: the len is {} but the index is {}",
                        self.size, i
                    );

                    if self.is_on(i) {
                        self.count_ones -= 1;

                        let (i, j) = self.inner_index(i);
                        self.buffer[i] -= 1 << j;

                        true
                    } else {
                        false
                    }
                }

                /// Set bits in the `range` to `0`.
                ///
                /// # Example
                /// ```
                /// use small_bitset::*;
                ///
                /// let mut bitset = bitset!(u64, 300);
                ///
                /// bitset.turn_on_range(0..300);
                /// assert_eq!(bitset.count_ones(), 300);
                /// bitset.turn_off_range(64..128);
                /// assert_eq!(bitset.count_zeros(), 64);
                /// ```
                ///
                /// # Panics
                /// Panics if `range `is out of bounds.
                ///
                /// # Time Complexity
                /// O(R/B), where R is size of `range` and B is the size of `Block` (e.g. 64 for u64).
                #[inline]
                pub fn turn_off_range(&mut self, range: Range<usize>) {
                    self.range_mut_with(range, |_| 0);
                }

                /// Reverses and then Returns `i`-th bit.
                ///
                /// # Panics
                /// Panics if `i` is out of bounds.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub fn toggle(&mut self, i: usize) -> bool {
                    assert!(
                        i < self.size,
                        "index out of bounds: the len is {} but the index is {}",
                        self.size, i
                    );

                    if self.is_on(i) {
                        self.count_ones -= 1;

                        let (i, j) = self.inner_index(i);
                        self.buffer[i] -= 1 << j;

                        false
                    }  else {
                        self.count_ones += 1;

                        let (i, j) = self.inner_index(i);
                        self.buffer[i] += 1 << j;

                        true
                    }
                }

                /// Set bits in the `range` to `0`.
                ///
                /// # Example
                /// ```
                /// use small_bitset::*;
                ///
                /// let mut bitset = bitset!(u64, 300);
                ///
                /// assert_eq!(bitset.count_ones(), 0);
                /// bitset.toggle_range(0..300);
                /// assert_eq!(bitset.count_ones(), 300);
                /// bitset.toggle_range(64..128);
                /// assert_eq!(bitset.count_zeros(), 64);
                /// ```
                ///
                /// # Panics
                /// Panics if `range `is out of bounds.
                ///
                /// # Time Complexity
                /// O(R/B), where R is size of `range` and B is the size of `Block` (e.g. 64 for u64).
                #[inline]
                pub fn toggle_range(&mut self, range: Range<usize>) {
                    self.range_mut_with(range, |block| !block);
                }

                /// Returns `true` is `i`-th bit is `1`, otherwise `false`.
                ///
                /// # Panics
                /// Panics if `i` is out of bounds.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub fn is_on(&self, i: usize) -> bool {
                    assert!(
                        i < self.size,
                        "index out of bounds: the len is {} but the index is {}",
                        self.size, i
                    );

                    let (i, j) = self.inner_index(i);
                    self.buffer[i] & (1 << j) != 0
                }

                /// Returns `true` is `i`-th bit is `0`, otherwise `false`.
                ///
                /// # Panics
                /// Panics if `i` is out of bounds.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub fn is_off(&self, i: usize) -> bool {
                    !self.is_on(i)
                }

                /// Returns `true` if all bits are `0`, otherwise `false`.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub const fn is_empty(&self) -> bool {
                    self.count_ones == 0
                }

                /// Returns `true` if all bits are `1`, otherwise `false`.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub const fn is_full(&self) -> bool {
                    self.count_ones == self.size as u32
                }

                /// Returns the number of ones.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub const fn count_ones(&self) -> u32 {
                    self.count_ones
                }

                /// Returns the number of ones within `range`.
                ///
                /// # Example
                /// ```
                /// use small_bitset::*;
                ///
                /// let mut bitset = bitset!(u32, 100);
                ///
                /// bitset.turn_on_range(0..50);
                /// assert_eq!(bitset.count_ones(), 50);
                /// assert_eq!(bitset.count_ones_range(25..75), 25);
                /// ```
                ///
                /// # Time Complexity
                /// O(R/B), where R is size of `range` and B is the size of `Block` (e.g. 64 for u64).
                pub fn count_ones_range(&self, range: Range<usize>) -> u32 {
                    let mut res = 0;
                    self.range_with(range, |block| res += block.count_ones());
                    res
                }

                /// Returns the number of zeros.
                ///
                /// # Time Complexity
                /// O(1)
                #[inline]
                pub const fn count_zeros(&self) -> u32 {
                    self.size as u32 - self.count_ones
                }

                /// Returns the number of zeros within `range`.
                ///
                /// # Example
                /// ```
                /// use small_bitset::*;
                ///
                /// let mut bitset = bitset!(u32, 100);
                ///
                /// bitset.turn_on_range(0..50);
                /// assert_eq!(bitset.count_zeros(), 50);
                /// assert_eq!(bitset.count_zeros_range(25..75), 25);
                /// ```
                ///
                /// # Time Complexity
                /// O(R/B), where R is size of `range` and B is the size of `Block` (e.g. 64 for u64).
                pub fn count_zeros_range(&self, range: Range<usize>) -> u32 {
                    (range.end - range.start) as u32 - self.count_ones_range(range)
                }

                /// Returns the number of trailing ones.
                /// `trailing_ones()` is short-circuiting.
                ///
                /// # Time Complexity
                /// O(N/B) in the worst case, where B is the size of `Block` (e.g. 64 for u64).
                #[inline]
                pub fn trailing_ones(&self) -> u32 {
                    let i = self.buffer.iter().take_while(|&&b| b == !0).count();

                    <$block>::BITS * i.saturating_sub(1) as u32 + self.buffer[i].trailing_ones()
                }

                /// Returns the number of trailing zeros.
                /// `trailing_zeros()` is short-circuiting.
                ///
                /// # Time Complexity
                /// O(N/B) in the worst case, where B is the size of `Block` (e.g. 64 for u64).
                #[inline]
                pub fn trailing_zeros(&self) -> u32 {
                    let i = self.buffer.iter().take_while(|&&b| b == 0).count();

                    <$block>::BITS * i.saturating_sub(1) as u32 + self.buffer[i].trailing_zeros()
                }
            }
        }
    )*};
}

bitset_impl! { u32 u64 u128 }
