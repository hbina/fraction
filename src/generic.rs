//! Integer generic traits and operations
//!
//! These traits and functions are for use in generic algorithms
//! that work indifferently to particular types, relying on
//! some common traits.

use super::{
    CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, /*Zero, One, */ Integer, ToPrimitive,
};
use std::cmp::PartialOrd;
use Sign;

#[cfg(feature = "with-bigint")]
use super::{BigInt, BigUint, One, Signed, Zero};

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};

/// Methods common to all integer types that
/// could be used generically in abstract algorithms
pub trait GenericInteger:
    'static
    + Sized
    + Integer
    + ToPrimitive
    + CheckedAdd
    + CheckedDiv
    + CheckedMul
    + CheckedSub
    + Add
    + Div
    + Mul
    + Rem
    + Sub
    + AddAssign
    + DivAssign
    + MulAssign
    + RemAssign
    + SubAssign
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Div<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> Rem<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> DivAssign<&'a Self>
    + for<'a> MulAssign<&'a Self>
    + for<'a> RemAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
{
    /// Returns value 0 of the type
    fn zero() -> Self;

    /// Returns value 1 of the type
    fn one() -> Self;

    /// Returns value 10 of the type
    fn ten() -> Self;

    /// Returns Maybe<static reference> of 0
    fn maybe_zero() -> Option<&'static Self>;

    /// Returns Maybe<static reference> of 1
    fn maybe_one() -> Option<&'static Self>;

    /// Returns Maybe<static reference> of 10
    fn maybe_ten() -> Option<&'static Self>;

    /// Returns the sign and the value itself.
    /// Zero values must have [Sign::Plus]
    fn get_signed_value(self) -> (Sign, Self);
}

#[cfg(feature = "with-bigint")]
lazy_static! {
    static ref _0_BU: BigUint = BigUint::zero();
    static ref _1_BU: BigUint = BigUint::one();
    static ref _10_BU: BigUint = BigUint::from(10u8);
    static ref _0_BI: BigInt = BigInt::zero();
    static ref _1_BI: BigInt = BigInt::one();
    static ref _10_BI: BigInt = BigInt::from(10i8);
}

#[cfg(feature = "with-bigint")]
impl GenericInteger for BigUint {
    #[inline]
    fn zero() -> Self {
        BigUint::zero()
    }
    #[inline]
    fn one() -> Self {
        BigUint::one()
    }
    #[inline]
    fn ten() -> Self {
        _10_BU.clone()
    }
    #[inline]
    fn maybe_zero() -> Option<&'static Self> {
        Some(&_0_BU)
    }
    #[inline]
    fn maybe_one() -> Option<&'static Self> {
        Some(&_1_BU)
    }
    #[inline]
    fn maybe_ten() -> Option<&'static Self> {
        Some(&_10_BU)
    }

    #[inline]
    fn get_signed_value(self) -> (Sign, Self) {
        (Sign::Plus, self)
    }
}

#[cfg(feature = "with-bigint")]
impl GenericInteger for BigInt {
    #[inline]
    fn zero() -> Self {
        BigInt::zero()
    }
    #[inline]
    fn one() -> Self {
        BigInt::one()
    }
    #[inline]
    fn ten() -> Self {
        _10_BI.clone()
    }
    #[inline]
    fn maybe_zero() -> Option<&'static Self> {
        Some(&_0_BI)
    }
    #[inline]
    fn maybe_one() -> Option<&'static Self> {
        Some(&_1_BI)
    }
    #[inline]
    fn maybe_ten() -> Option<&'static Self> {
        Some(&_10_BI)
    }

    #[inline]
    fn get_signed_value(self) -> (Sign, Self) {
        (
            if self.is_negative() {
                Sign::Minus
            } else {
                Sign::Plus
            },
            self,
        )
    }
}

macro_rules! generic_integer_for_uint {
    ($t:ty) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self {
                0
            }
            #[inline]
            fn one() -> Self {
                1
            }
            #[inline]
            fn ten() -> Self {
                10
            }
            #[inline]
            fn maybe_zero() -> Option<&'static Self> {
                None
            }
            #[inline]
            fn maybe_one() -> Option<&'static Self> {
                None
            }
            #[inline]
            fn maybe_ten() -> Option<&'static Self> {
                None
            }

            #[inline]
            fn get_signed_value(self) -> (Sign, Self) {
                (Sign::Plus, self)
            }
        }
    };
}

generic_integer_for_uint!(u8);
generic_integer_for_uint!(u16);
generic_integer_for_uint!(u32);
generic_integer_for_uint!(u64);
generic_integer_for_uint!(u128);
generic_integer_for_uint!(usize);

macro_rules! generic_integer_for_int {
    ($t:ty) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self {
                0
            }
            #[inline]
            fn one() -> Self {
                1
            }
            #[inline]
            fn ten() -> Self {
                10
            }
            #[inline]
            fn maybe_zero() -> Option<&'static Self> {
                None
            }
            #[inline]
            fn maybe_one() -> Option<&'static Self> {
                None
            }
            #[inline]
            fn maybe_ten() -> Option<&'static Self> {
                None
            }

            #[inline]
            fn get_signed_value(self) -> (Sign, Self) {
                (
                    if self.is_negative() {
                        Sign::Minus
                    } else {
                        Sign::Plus
                    },
                    self,
                )
            }
        }
    };
}

generic_integer_for_int!(i8);
generic_integer_for_int!(i16);
generic_integer_for_int!(i32);
generic_integer_for_int!(i64);
generic_integer_for_int!(i128);
generic_integer_for_int!(isize);

/// Builds integer of type T from another integer of type F in a generic way
///
/// Allows safe runtime conversions between integer types when it's not possible
/// statically. E.g: `i8 -> u8`, `u8 -> i8`, `usize -> u8` or even `BigUint -> u8` and so on.
///
/// # Examples
///
/// ```
/// use fraction::{Sign, generic::read_generic_integer};
///
/// assert_eq!((Sign::Plus, 127i8), read_generic_integer(127u8).unwrap());
/// assert_eq!((Sign::Minus, 128u8), read_generic_integer(-128i8).unwrap());
/// assert_eq!((Sign::Minus, 255u8), read_generic_integer(-255isize).unwrap());
/// ```
pub fn read_generic_integer<T, F>(val: F) -> Option<(Sign, T)>
where
    F: GenericInteger + PartialOrd,
    T: GenericInteger,
{
    let (sign, mut val) = val.get_signed_value();

    let mut vptr: F = F::one();
    let mut rptr: T = T::one();
    let mut result: T = T::zero();

    loop {
        vptr = match F::maybe_ten().map_or_else(
            || vptr.checked_mul(&GenericInteger::ten()),
            |_10| vptr.checked_mul(_10),
        ) {
            Some(v) => v,
            None => break,
        };

        let vdelta: F = val.checked_sub(&val.checked_div(&vptr)?.checked_mul(&vptr)?)?;

        let mut rdelta: T = T::zero();

        let mut vldelta: F = vdelta.checked_div(&F::maybe_ten().map_or_else(
            || vptr.checked_div(&GenericInteger::ten()),
            |_10| vptr.checked_div(_10),
        )?)?;

        loop {
            if F::maybe_zero().map_or_else(|| vldelta == GenericInteger::zero(), |v| vldelta == *v)
            {
                break;
            }

            rdelta = T::maybe_one().map_or_else(
                || rdelta.checked_add(&T::one()),
                |_1| rdelta.checked_add(_1),
            )?;

            vldelta = F::maybe_one().map_or_else(
                || {
                    if sign == Sign::Plus {
                        vldelta.checked_sub(&GenericInteger::one())
                    } else {
                        vldelta.checked_add(&GenericInteger::one())
                    }
                },
                |_1| {
                    if sign == Sign::Plus {
                        vldelta.checked_sub(_1)
                    } else {
                        vldelta.checked_add(_1)
                    }
                },
            )?;
        }

        result = result.checked_add(&rdelta.checked_mul(&rptr)?)?;
        val = val.checked_sub(&vdelta)?;

        if F::maybe_zero().map_or_else(|| val == GenericInteger::zero(), |_0| val == *_0) {
            break;
        }

        rptr = T::maybe_ten().map_or_else(
            || rptr.checked_mul(&GenericInteger::ten()),
            |_10| rptr.checked_mul(_10),
        )?;
    }

    if F::maybe_zero().map_or_else(|| val != GenericInteger::zero(), |_0| val != *_0) {
        let mut vldelta: F = val.checked_div(&vptr)?;

        let mut rdelta: T = T::zero();

        loop {
            if F::maybe_zero()
                .map_or_else(|| vldelta == GenericInteger::zero(), |_0| vldelta == *_0)
            {
                break;
            }

            rdelta = T::maybe_one().map_or_else(
                || rdelta.checked_add(&GenericInteger::one()),
                |_1| rdelta.checked_add(_1),
            )?;

            vldelta = F::maybe_one().map_or_else(
                || {
                    if sign == Sign::Plus {
                        vldelta.checked_sub(&GenericInteger::one())
                    } else {
                        vldelta.checked_add(&GenericInteger::one())
                    }
                },
                |_1| {
                    if sign == Sign::Plus {
                        vldelta.checked_sub(_1)
                    } else {
                        vldelta.checked_add(_1)
                    }
                },
            )?;
        }
        result = result.checked_add(&rdelta.checked_mul(&rptr)?)?;
    }

    Some((sign, result))
}

#[cfg(test)]
mod tests {
    // TODO: tests

    use super::*;

    #[test]
    fn max_to_max() {
        let (s, v) = read_generic_integer::<u32, u32>(u32::max_value()).unwrap();
        assert_eq!(s, Sign::Plus);
        assert_eq!(v, u32::max_value());
    }

    #[test]
    fn sign() {
        let (s, _) = read_generic_integer::<i8, i8>(0i8).unwrap();
        assert_eq!(s, Sign::Plus);

        let (s, _) = read_generic_integer::<i8, i8>(1i8).unwrap();
        assert_eq!(s, Sign::Plus);

        let (s, _) = read_generic_integer::<i8, i8>(-1i8).unwrap();
        assert_eq!(s, Sign::Minus);
    }
}
