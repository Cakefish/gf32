use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::num::NonZeroU32;
use thiserror::Error;

#[derive(Error, Debug)]
#[error("NaN or Infinity disallowed")]
pub struct InvalidError;

/// An opinionated f32 for game values.
///
/// -0.0 is converted to 0.0
/// Subnormals are rounded to 0.0
/// Inf and NaN is disallowed.
///
/// Option<Gf32> is memory optimized.
///
/// Supports sane ordering, equality and hashing.
///
/// Beyond that, inside Gf32 is just a plain old f32.
///
/// This is a storage only value. Use g32.into() to convert it to a normal f32 for use in
/// calculations.
///
/// The only time Gf32 is not bit-identical with f32 is when it is storing a 0.0 value. In this case
/// Gf32 actually stores a -0.0 instead. This is because 0.0 is all zero bits, and all zero bits is
/// reserved for then None value of Option<Gf32>. The -0.0 is converted to 0.0 when users attempt to
/// get the f32 value from Gf32.
///
#[derive(Clone, Copy)]
pub struct Gf32 {
    data: NonZeroU32,
}

const ZERO_PATTERN: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;

impl Gf32 {
    /// Create a new Gf32 from a given value.
    ///
    /// Returns Ok(Gf32) or Err if the provided value is a NaN or Infinite.
    pub fn try_new(value: f32) -> Result<Self, InvalidError> {
        let bits = value.to_bits();
        const FRACTION_MASK: u32 = 0x7f800000;
        let fraction = bits & FRACTION_MASK;

        // NaN and Infinity not allowed
        if fraction == FRACTION_MASK {
            return Err(InvalidError {});
        }

        // 0.0, -0.0 and all subnormals are converted to a singular 0.0 value.
        // The conversions are assumed to be irrelevant for users of Gf32.
        if fraction == 0 {
            return Ok(Default::default());
        }

        // SAFETY: The only value with with all zero binary bits is handled above.
        unsafe {
            Ok(Self {
                data: NonZeroU32::new_unchecked(bits),
            })
        }
    }

    /// Create a new Gf32 from a given value.
    ///
    /// Panics if the provided value is a NaN or Infinite.
    ///
    /// This is provided due to the expectation that most users of Gf32 would just unwrap anyway.
    /// `try_new` and TryFrom is provided for users that do want to check.
    #[inline]
    pub fn new(value: f32) -> Self {
        Self::try_new(value).expect("value contains NaN or Infinite")
    }

    /// Create a new Gf32 from its inner representation.
    ///
    /// # Safety
    /// This is unsafe because the argument may contain NaN, Inf etc.
    #[inline]
    pub unsafe fn from_raw(inner: NonZeroU32) -> Self {
        Self { data: inner }
    }

    /// Retreive the f32 from Gf32
    #[inline]
    pub fn get(&self) -> f32 {
        // Non branching swap of our sentinel -0.0 with 0.0
        let bits = self.data.get();
        let mask = ((bits == 0x80000000) as u32) << 31;
        f32::from_bits(bits ^ mask)
    }

    /// Retreives the f32 but does **NOT** convert -0.0 to 0.0
    ///
    /// This is used internally to make Ord/Eq etc a bit quicker, since it doesn't matter if it is
    /// doing < 0.0 or < -0.0 or -0.0 == -0.0 (as long as there exists only either 0.0 or -0.0)
    ///
    /// External users can also use this function if they for some reason have extreme performance
    /// needs and don't care that 0.0 returns as -0.0
    ///
    /// This function is fast because it literally does nothing beyond re-interpreting the type.
    #[inline]
    pub fn get_no_conversion(&self) -> f32 {
        f32::from_bits(self.data.get())
    }

    /// Returns Gf32 as u32 bits.
    #[inline]
    pub fn to_bits(&self) -> u32 {
        self.data.get()
    }

    /// Recreate from the `to_bits()` method.
    #[inline]
    pub fn from_bits(bits: u32) -> Option<Self> {
        Self::try_new(f32::from_bits(bits)).ok()
    }

    /// Recreate from the `to_bits()` method unchecked.
    ///
    /// # Safety
    /// This is unsafe because the argument may contain NaN, Inf etc.
    ///
    /// To safely create Gf32 from bits do "Gf32::from_bits"
    #[inline]
    pub unsafe fn from_bits_unchecked(bits: u32) -> Self {
        // SAFETY: bits has to result in a valid Gf32, i.e. no INF or NAN values.
        unsafe { Self::from_raw(NonZeroU32::new_unchecked(bits)) }
    }
}

impl PartialEq for Gf32 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // This works because a floating point representation
        // will ever only have one equivalent bit representation
        // in our case, since we do not allow positive zero, NaN
        // or infinity.
        self.data == other.data
    }
}

impl Eq for Gf32 {}

impl PartialOrd for Gf32 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Gf32 {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.get_no_conversion()
            .partial_cmp(&other.get_no_conversion())
            .expect("cannot fail as we do not have NaN")
    }
}

impl fmt::Debug for Gf32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Gf32{{{}}}", self.get())
    }
}

impl fmt::Display for Gf32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

impl Default for Gf32 {
    #[inline]
    fn default() -> Self {
        // Passing a const into a const func is just as good as the unchecked version.
        Self {
            data: NonZeroU32::new(ZERO_PATTERN).unwrap(),
        }
    }
}

impl Hash for Gf32 {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.data.hash(state);
    }
}

impl From<Gf32> for f32 {
    #[inline]
    fn from(value: Gf32) -> Self {
        value.get()
    }
}

impl TryFrom<f32> for Gf32 {
    type Error = InvalidError;

    #[inline]
    fn try_from(value: f32) -> Result<Self, Self::Error> {
        Gf32::try_new(value)
    }
}

#[cfg(feature = "bauble")]
mod bauble_impl {
    use super::*;
    use bauble::ValueKind;

    impl<'a, A: bauble::BaubleAllocator<'a>> bauble::FromBauble<'a, A> for Gf32 {
        const INFO: bauble::TypeInfo<'static> = bauble::TypeInfo::Kind(ValueKind::Num);

        fn from_bauble(
            data: bauble::Val,
            allocator: &A,
        ) -> Result<A::Out<Self>, Box<bauble::DeserializeError>> {
            match data.value.value {
                bauble::Value::Num(num) => {
                    Self::try_new(
                        num.try_into()
                            .map_err(|e| bauble::DeserializeError::Custom {
                                message: format!("converting Decimal to f32 error: {e}"),
                                span: data.value.span,
                            })?,
                    )
                    .map_err(|e| {
                        Box::new(bauble::DeserializeError::Custom {
                            message: format!("error wrapping f32 into Gf32: {e}"),
                            span: data.value.span,
                        })
                    })
                    // SAFETY: there are no allocations in Gf32, so this doesn't do anything.
                    .map(|v| unsafe { allocator.wrap(v) })
                }
                _ => Err(Box::new(bauble::DeserializeError::WrongKind {
                    expected: ValueKind::Num,
                    found: data.value.kind(),
                    ty: bauble::OwnedTypeInfo::Kind(ValueKind::Num),
                    span: data.value.span,
                })),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f32;

    #[test]
    fn gf32_conversion_test() {
        for i in 0u32..=u32::MAX {
            let f = f32::from_bits(i);

            if f.is_infinite() || f.is_nan() {
                // Inf or NaN should panic
                assert!(Gf32::try_new(f).is_err());
            } else if f == 0.0 || f == -0.0 || f.is_subnormal() {
                // 0.0, -0.0 and subnormals should become 0.0
                assert_eq!(Gf32::new(f).get(), 0.0);
            } else {
                // All other values should convert back and forth without loss
                let g = Gf32::new(f);
                assert_eq!(g.get(), f);
            }
        }
    }

    #[test]
    fn gf32_comparison_test() {
        let values = vec![
            f32::MIN,
            f32::MIN_POSITIVE,
            -1.0,
            -f32::EPSILON,
            -0.0,
            0.0,
            f32::EPSILON,
            1.0,
            f32::MAX,
            2304.2,
            99999.999999,
            1234.0,
            0.00000001,
            u16::MAX as f32,
        ];

        for &a in &values {
            let ga = Gf32::new(a);
            for &b in &values {
                let gb = Gf32::new(b);

                assert_eq!(ga == gb, a == b);
                assert_eq!(ga != gb, a != b);
                assert_eq!(ga < gb, a < b);
                assert_eq!(ga <= gb, a <= b);
                assert_eq!(ga > gb, a > b);
                assert_eq!(ga >= gb, a >= b);

                assert_eq!(ga.cmp(&gb), a.partial_cmp(&b).unwrap());
            }
        }
    }
}
