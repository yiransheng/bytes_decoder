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

        // Replacement Grammar
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

        let decoder = Byte::new(b'2').void(); // S0
        let decoder = next_level(decoder); // S1
        let decoder = next_level(decoder); // S2
        let decoder = next_level(decoder); // S3
        let decoder = next_level(decoder); // S4
        let decoder = next_level(decoder); // S5

        let ok_input = "[2[[2]22]]".as_bytes();
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
    fn test_nested_trait_obj() {
        // Now use trait objects instead..

        type BoxDecode<'b> = Box<Decode<'b, Output = ()>>;

        fn next_level_boxed<D: 'static + Decode<'static, Output = ()>>(
            term: D,
            prev_level: BoxDecode<'static>,
        ) -> BoxDecode<'static> {
            let ret = term.or(Byte::new(b'[')
                .and(prev_level.many_())
                .and_(Byte::new(b']')));

            Box::new(ret)
        }

        let base = Byte::new(b'2').void();
        // explicity type anotation is necessary to erase the type
        let mut decoder: BoxDecode<'static> = Box::new(base.clone());

        // sky is the limit!
        for _ in 0..4096 {
            decoder = next_level_boxed(base.clone(), decoder);
        }
        drop(base);

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
}
