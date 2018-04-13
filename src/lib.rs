pub mod decode;
pub mod primitives;

#[cfg(test)]
mod tests {
    use super::decode::{Decode, DecodeError};
    use super::primitives::*;

    #[test]
    fn test_nested() {
        #[inline]
        fn next_level<'b, D>(prev_level: D) -> impl Decode<'b, Output = ()>
        where
            D: Decode<'b, Output = ()>,
        {
            let term = Byte::new(b'2').void();

            term.or(Byte::new(b'[')
                .and(prev_level.many_())
                .and_(Byte::new(b']')))
        }

        let t0 = Byte::new(b'2').void();
        let t1 = next_level(t0);
        let t2 = next_level(t1);
        let t3 = next_level(t2);
        let t4 = next_level(t3);
        let t5 = next_level(t4);

        let ok_input = "[2[[2]22]]".as_bytes();
        let partial_input = "[[22[2]]".as_bytes();
        let bad_input = "[2][22]".as_bytes();

        assert_eq!(t5.decode_exact(ok_input), Ok(()));
        assert_eq!(t5.decode_exact(partial_input), Err(DecodeError::Incomplete));
        assert_eq!(t5.decode_exact(bad_input), Err(DecodeError::Fail));
    }
}
