pub mod decode;
pub mod primitives;

pub use decode::{Decode, DecodeError};

#[cfg(test)]
mod tests {
    use super::decode::{Decode, DecodeError};
    use super::primitives::*;

    #[test]
    fn test_nested() {
        // The goal is to recognize CFG grammar G:
        //
        // S -> 2 | [ <elements> ]
        // elements -> S*
        //
        // Example sentence: [2[22][[]2]2[2]2222]
        //
        // However, naive implemenation requires infinite many types!
        //
        // (when evalulating `impl Decode<'b, Output=()>`)

        // Grammar
        //
        // S0 -> 2
        // S1 -> 2 | [ S0* ]
        // S2 -> 2 | [ S1* ]
        // S_k -> 2 | [ S_{k-1}* ]
        // ...
        //
        // S_n is grammar G with max nest depth restricted to at most n

        // calling this more than a handful of times will blow up..
        // (S9 killed my computer... rustc crashed)
        #[allow(dead_code)]
        fn next_level<'b, D>(prev_level: D) -> impl Decode<'b, Output = ()>
        where
            D: Decode<'b, Output = ()>,
        {
            let term = Byte::new(b'2').void();

            term.or(Byte::new(b'[')
                .and(prev_level.many_())
                .and_(Byte::new(b']')))
        }

        type Boxed<'b> = Box<Decode<'b, Output = ()>>;

        // um... use trait obj instead
        fn next_level_boxed<'b>(prev_level: Boxed<'static>) -> Boxed<'static> {
            let term = Byte::new(b'2').void();

            let ret = term.or(Byte::new(b'[')
                .and(prev_level.many_())
                .and_(Byte::new(b']')));

            Box::new(ret)
        }

        let decoder = Byte::new(b'2').void(); // S0
        let mut decoder: Boxed<'static> = Box::new(decoder);

        for _ in 0..4096 {
            decoder = next_level_boxed(decoder);
        }

        // let ok_input = "[2[[2]22]]".as_bytes();
        let ok_input = "[[[[[[[[[2[[2]22]]]]]]]]]]".as_bytes();
        let partial_input = "[[22[2][]]".as_bytes();
        let bad_input = "[2][22]".as_bytes();

        assert_eq!(decoder.decode_exact(ok_input), Ok(()));
        assert_eq!(
            decoder.decode_exact(partial_input),
            Err(DecodeError::Incomplete)
        );
        assert_eq!(decoder.decode_exact(bad_input), Err(DecodeError::Fail));
    }

    #[test]
    fn test_using() {
        fn decode_using<'b>(
            one: &Decode<'b, Output = ()>,
            open: &Decode<'b, Output = ()>,
            close: &Decode<'b, Output = ()>,
            bytes: &'b [u8],
        ) -> Result<(&'b [u8], ()), DecodeError> {
            let result = one.decode(bytes);

            match result {
                x @ Ok(_) => x,
                _ => {
                    let (remainder, _) = open.decode(bytes)?;
                    let mut bytes = remainder;
                    loop {
                        match decode_using(one, open, close, bytes) {
                            Ok((remainder, _)) => {
                                bytes = remainder;
                            }
                            _ => break,
                        }
                    }
                    close.decode(bytes)
                }
            }
        }
        fn decode_exact_using<'b>(
            one: &Decode<'b, Output = ()>,
            open: &Decode<'b, Output = ()>,
            close: &Decode<'b, Output = ()>,
            bytes: &'b [u8],
        ) -> Result<(&'b [u8], ()), DecodeError> {
            let (remainder, _) = decode_using(one, open, close, bytes)?;

            if remainder.len() > 0 {
                Err(DecodeError::Fail)
            } else {
                Ok((remainder, ()))
            }
        }

        let two = Byte::new(b'2').void();
        let open = Byte::new(b'[').void();
        let close = Byte::new(b']').void();

        let ok_input = "[[[[[[[[[2[[2]22]]]]]]]]]]".as_bytes();
        let bad_input = "[2][22]".as_bytes();

        assert_eq!(
            decode_exact_using(&two, &open, &close, ok_input).is_ok(),
            true
        );
        assert_eq!(
            decode_exact_using(&two, &open, &close, bad_input),
            Err(DecodeError::Fail)
        );
    }
}
