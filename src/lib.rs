pub mod decode;
pub mod primitives;

#[cfg(test)]
mod tests {
    use super::decode::{Decode, DecodeError};
    use super::primitives::*;

    #[test]
    fn test_nested() {
        let two = Byte::new(b'2').void();

        #[derive(Clone)]
        struct Rec1<D> {
            inner: D,
        }
        impl<'b, D: Decode<'b>> Decode<'b> for Rec1<D> {
            type Output = D::Output;

            #[inline]
            fn decode<'a>(
                &'a self,
                bytes: &'b [u8],
            ) -> Result<(&'b [u8], Self::Output), DecodeError> {
                self.inner.decode(bytes)
            }
        }
        #[derive(Clone)]
        struct Rec2<D> {
            inner: D,
        }
        impl<'b, D: Decode<'b>> Decode<'b> for Rec2<D> {
            type Output = D::Output;

            #[inline]
            fn decode<'a>(
                &'a self,
                bytes: &'b [u8],
            ) -> Result<(&'b [u8], Self::Output), DecodeError> {
                self.inner.decode(bytes)
            }
        }
        #[derive(Clone)]
        struct Rec3<D> {
            inner: D,
        }
        impl<'b, D: Decode<'b>> Decode<'b> for Rec3<D> {
            type Output = D::Output;

            #[inline]
            fn decode<'a>(
                &'a self,
                bytes: &'b [u8],
            ) -> Result<(&'b [u8], Self::Output), DecodeError> {
                self.inner.decode(bytes)
            }
        }

        fn nest3<'b, D: Clone + Decode<'b, Output = ()>>(
            decoder: Rec3<D>,
        ) -> impl Decode<'b, Output = ()> {
            decoder.or_else_then(|decoder| {
                let open = Byte::new(b'[').void();
                let close = Byte::new(b']').void();
                let d2 = Rec2 {
                    inner: decoder.inner.clone(),
                };
                let inner = decoder.or(nest2(d2));

                open.and(inner.many_()).and(close)
            })
        }
        fn nest2<'b, D: Clone + Decode<'b, Output = ()>>(
            decoder: Rec2<D>,
        ) -> impl Decode<'b, Output = ()> {
            decoder.or_else_then(|decoder| {
                let open = Byte::new(b'[').void();
                let close = Byte::new(b']').void();
                let d1 = Rec1 {
                    inner: decoder.inner.clone(),
                };
                let inner = decoder.or(nest1(d1));

                open.and(inner.many_()).and(close)
            })
        }
        fn nest1<'b, D: Clone + Decode<'b, Output = ()>>(
            decoder: Rec1<D>,
        ) -> impl Decode<'b, Output = ()> {
            decoder.or_else_then(|decoder| {
                let open = Byte::new(b'[').void();
                let close = Byte::new(b']').void();
                let inner = decoder.inner;

                open.and(inner.many_()).and(close)
            })
        }

        let inputs = "[2[2][[]]]".as_bytes();

        let result = nest3(Rec3 { inner: two }).decode_exact(inputs);

        assert_eq!(result, Ok(()));
    }
}
