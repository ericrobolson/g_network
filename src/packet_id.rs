use core::ops::Sub;

pub(crate) type Inner = u16;

/// An id for a packet.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct PacketId(Inner);
impl PacketId {
    /// Decrements the given packet
    pub(crate) fn decrement(&self) -> Self {
        *self - 1.into()
    }

    /// Decrements the given packet
    pub(crate) fn decrement_n(&self, n: Inner) -> Self {
        Self(self.inner().wrapping_sub(n))
    }

    /// Increments the packet
    pub(crate) fn increment(&self) -> Self {
        Self(self.0.wrapping_add(1))
    }

    /// Returns the inner value for the packet id
    pub(crate) fn inner(&self) -> Inner {
        self.0
    }

    /// Returns a usize of this value
    pub(crate) fn usize(&self) -> usize {
        self.inner() as usize
    }

    /// Returns whether the current packet is greater than another packet.
    pub fn is_greater(&self, other: Self) -> bool {
        // https://www.rfc-editor.org/rfc/rfc1982
        /*
        s1 is said to be greater than s2 if, and only if, s1 is not equal to
        s2, and

             (i1 < i2 and i2 - i1 > 2^(SERIAL_BITS - 1)) or
             (i1 > i2 and i1 - i2 < 2^(SERIAL_BITS - 1))
        */

        let i1 = self.inner();
        let i2 = other.inner();

        // const SERIAL_BITS: u32 = 16;
        const TWO_POW15: u16 = 32768; // 2_u16.pow(SERIAL_BITS - 1);

        (i1 < i2 && i2 - i1 > TWO_POW15) || (i1 > i2 && i1 - i2 < TWO_POW15)
    }
}

impl Sub for PacketId {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let diff = self.0.wrapping_sub(rhs.0);
        Self(diff)
    }
}

impl From<Inner> for PacketId {
    fn from(u: Inner) -> Self {
        Self(u)
    }
}

impl From<i32> for PacketId {
    fn from(u: i32) -> Self {
        Self(u as Inner)
    }
}
impl From<usize> for PacketId {
    fn from(u: usize) -> Self {
        Self(u as Inner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    describe!(increment => {
        #[test]
        fn increment_adds_one() {
            assert_eq!(PacketId(4), PacketId(3).increment());
        }

        #[test]
        fn increment_wraps() {
            assert_eq!(PacketId(0), PacketId(Inner::MAX).increment());
        }
    });

    mod decrement {
        use super::*;

        #[test]
        fn should_decrement() {
            let expected: PacketId = 3.into();
            let actual: PacketId = PacketId(4).decrement();
            assert_eq!(expected, actual);
        }

        #[test]
        fn should_decrement_and_wrap() {
            let expected: PacketId = (Inner::MAX).into();
            let actual: PacketId = PacketId(0).decrement();
            assert_eq!(expected, actual);
        }
    }

    mod decrement_n {
        use super::*;

        #[test]
        fn should_decrement() {
            let expected: PacketId = 1.into();
            let actual: PacketId = PacketId(4).decrement_n(3);
            assert_eq!(expected, actual);
        }

        #[test]
        fn should_decrement_and_wrap() {
            let n = 344;
            let expected: PacketId = (Inner::MAX).into();
            let actual: PacketId = PacketId(Inner::MAX.wrapping_add(n)).decrement_n(n);
            assert_eq!(expected, actual);
        }
    }

    mod sub {
        use super::*;

        #[test]
        fn sub_should_subtract() {
            let expected: PacketId = 3.into();
            let actual: PacketId = PacketId(6) - PacketId(3);
            assert_eq!(expected, actual);
        }

        #[test]
        fn sub_should_subtract_and_wrap() {
            let expected: PacketId = (Inner::MAX - 1).into();
            let actual: PacketId = PacketId(1) - PacketId(3);
            assert_eq!(expected, actual);
        }
    }

    mod is_greater {
        use super::*;

        #[test]
        fn two_greater_than_one() {
            let a: PacketId = 2.into();
            let b: PacketId = 1.into();
            assert_eq!(true, a.is_greater(b));
            assert_eq!(false, b.is_greater(a));
        }

        #[test]
        fn test_5_greater_than_65000() {
            let a: PacketId = 5.into();
            let b: PacketId = 65000.into();
            assert_eq!(true, a.is_greater(b));
            assert_eq!(false, b.is_greater(a));
        }
    }
}
