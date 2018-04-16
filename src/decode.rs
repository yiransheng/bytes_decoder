use std::default::Default;
use std::marker::PhantomData;
use std::rc::Rc;

#[derive(Debug, Eq, PartialEq)]
pub enum DecodeError {
    Incomplete,
    Fail,
}

fn _assert_is_object_safe(_: &Decode<Output = ()>) {}

/// An interface for building decoders operating on a borrowed bytes slice.
///
/// Inspired by [monadic parser combinators] common in Haskell, and tries to follow
/// conventions established by [`std::iter::Iterator`].
///
/// This trait is generic over lifetime `'b`, which represents the lifetime
/// of borrowed `&[u8]` its `decode` method operates on. This allows associated
/// `Output` type to be references of this lifetime, for example produce a
/// sub-slice of the input as output.
///
pub trait Decode<'b> {
    /// [monadic parser combinators]: http://www.cs.nott.ac.uk/~pszgmh/monparsing.pdf
    /// The type of value produced by a decoder
    type Output;

    /// Decode a sequence of bytes, return a tuple of (remaining bytes, output) if successful.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "hello world!".as_bytes();
    /// let decoder = BytesExact::new("hello".as_bytes());
    ///
    /// assert!(decoder.decode(input).is_ok());
    ///
    /// ```
    ///
    /// #Errors
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError>;

    /// Decode bytes, discard remainder and only return [Ok(`Self::Output`)] if successful.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "hello world!".as_bytes();
    /// let decoder = BytesExact::new("hello".as_bytes());
    ///
    /// assert_eq!(
    ///     decoder.decode_(input),
    ///     Ok("hello".as_bytes())
    /// );
    ///
    /// ```
    #[inline]
    fn decode_<'a>(&'a self, bytes: &'b [u8]) -> Result<Self::Output, DecodeError> {
        let (_, out) = self.decode(bytes)?;
        Ok(out)
    }

    /// Similar to [`decode_`], but fails if input bytes is not consumed entirely.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "hello world!".as_bytes();
    /// let input_exact = "hello".as_bytes();
    ///
    /// let decoder = BytesExact::new("hello".as_bytes());
    ///
    /// assert!(decoder.decode_exact(input).is_err());
    /// assert!(decoder.decode_exact(input_exact).is_ok());
    ///
    /// ```
    #[inline]
    fn decode_exact<'a>(&'a self, bytes: &'b [u8]) -> Result<Self::Output, DecodeError> {
        let (remainder, out) = self.decode(bytes)?;
        if remainder.len() == 0 {
            Ok(out)
        } else {
            Err(DecodeError::Fail)
        }
    }

    /// Creates a Decode behaves identical to this one, but discards Output, and returns Ok(())
    /// if successful.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input_exact = "hello".as_bytes();
    ///
    /// let decoder = BytesExact::new("hello".as_bytes()).void();
    ///
    /// assert_eq!(decoder.decode_exact(input_exact), Ok(()));
    ///
    /// ```
    #[inline]
    fn void(self) -> Void<Self>
    where
        Self: Sized,
    {
        Void { src: self }
    }

    /// Creates a Decode behaves identical to this one, but reports number of bytes consumed.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input_exact = "hello".as_bytes();
    ///
    /// let decoder = BytesExact::new("hello".as_bytes()).bytes_consumed();
    ///
    /// assert_eq!(decoder.decode_exact(input_exact), Ok(5));
    ///
    /// ```
    #[inline]
    fn bytes_consumed(self) -> BytesConsumed<Self>
    where
        Self: Sized,
    {
        BytesConsumed { src: self }
    }
    #[inline]
    fn filter_map<T, F>(self, f: F) -> FilterMap<Self, F>
    where
        F: Fn(Self::Output) -> Option<T>,
        Self: Sized,
    {
        FilterMap { src: self, f }
    }

    /// Create a Decode object behaves like self if output evaluated by supplied closure is
    /// true, otherwise fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "Hello".as_bytes();
    ///
    /// let decoder = ByteAny
    ///     .repeat(5)
    ///     .filter(|bs| bs.len() == 4);
    ///
    /// assert!(decoder.decode_exact(input).is_err());
    ///
    /// ```
    #[inline]
    fn filter<F>(self, f: F) -> Filter<Self, F>
    where
        F: Fn(&Self::Output) -> bool,
        Self: Sized,
    {
        Filter { src: self, f }
    }

    /// Create a Decode that maps current output with a closure (consumes Output).
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "Hello".as_bytes();
    ///
    /// let decoder = ByteAny
    ///     .repeat(5)
    ///     .map::<Vec<u8>, _>(|mut xs| {
    ///         xs.reverse();
    ///         xs
    ///     });
    ///
    /// assert_eq!(
    ///     decoder.decode_exact(input),
    ///     Ok(b"olleH".to_vec())
    /// );
    ///
    /// ```
    #[inline]
    fn map<B, F>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Output) -> B,
        Self: Sized,
    {
        Map { src: self, f }
    }

    /// Create a Decode that parses the slice it consumed with a given closure.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "Hello".as_bytes();
    ///
    /// let decoder = ByteAny
    ///     .repeat(5)
    ///     .parse_slice(|s| String::from_utf8(s.to_vec()).unwrap());
    ///
    /// assert_eq!(decoder.decode_exact(input), Ok("Hello".to_string()));
    ///
    /// ```
    #[inline]
    fn parse_slice<B, F>(self, f: F) -> ParseSlice<Self, F>
    where
        F: Fn(&'b [u8]) -> B,
        Self: Sized,
    {
        ParseSlice { src: self, f }
    }

    /// Create a Decode that "returns" the slice it consumed in a zero-copy manner.
    ///
    /// # Examples
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    /// let input = "Hello".as_bytes();
    ///
    /// let decoder = ByteAny
    ///     .repeat(5)
    ///     .to_consumed_slice();
    ///
    /// assert_eq!(decoder.decode_exact(input), Ok("Hello".as_bytes()));
    ///
    /// ```
    #[inline]
    fn to_consumed_slice(self) -> ToSlice<Self>
    where
        Self: Sized,
    {
        ToSlice { src: self }
    }

    #[inline]
    fn and_then<B, F>(self, f: F) -> FlatMap<Self, F>
    where
        B: Decode<'b>,
        F: Fn(Self::Output) -> B,
        Self: Sized,
    {
        FlatMap { src: self, f }
    }
    #[inline]
    fn and_then_<B, F>(self, f: F) -> FlatMap_<Self, F>
    where
        B: Decode<'b>,
        F: Fn(&Self::Output) -> B,
        Self: Sized,
    {
        FlatMap_ { src: self, f }
    }
    #[inline]
    fn and<B: Decode<'b>>(self, snd: B) -> AndNext<Self, B>
    where
        Self: Sized,
    {
        AndNext { fst: self, snd }
    }
    #[inline]
    fn and_<B: Decode<'b>>(self, snd: B) -> AndNext_<Self, B>
    where
        Self: Sized,
    {
        AndNext_ { fst: self, snd }
    }

    #[inline]
    fn or<B: Decode<'b, Output = Self::Output>>(self, other: B) -> Alternative<Self, B>
    where
        Self: Sized,
    {
        Alternative { a: self, b: other }
    }

    /// Create a Decode (name if d_next), with the current one as a base decoder. If current
    /// decoder succeeds returns output, otherwise apply a given closure to `d_next` and use
    /// the resulting decoder.
    ///
    /// Imagine a decoder for nested parentheses (but not emtpy bytes).
    ///
    /// ```ignore
    ///
    /// let open = Byte::new(b'(');
    /// let close = Byte::new(b')');
    ///
    /// LHS = BytesExact::new(b"()")
    ///         .or( open.and(LHS).and_(close) );
    ///
    /// ```
    ///
    /// `LHS` is used in combinators before it is created. Rust is not Haskell
    /// with lazy evaluation, ideas like this is painful to express.
    ///
    /// `or_else_recur` provides a way:
    ///
    /// ```
    /// use ::bytes_decoder::*;
    /// use ::bytes_decoder::primitives::*;
    ///
    ///
    /// let parens = BytesExact::new(b"()").or_else_recur(|parens| {
    ///    let open = Byte::new(b'(');
    ///    let close = Byte::new(b')');
    ///
    ///    open
    ///      .and(parens)
    ///      .and_(close)
    /// });
    ///
    /// let input = "(((())))".as_bytes();
    ///
    /// assert!(parens.decode_exact(input).is_ok());
    ///
    /// ```
    ///
    /// Note: this is achieved using `Rc` and trait object, I have struggled
    /// quite a lot ot get a working version in safe rust. One day, I might
    /// find a more efficient solution with contraints present.
    #[inline]
    fn or_else_recur<E: 'static, F: 'static>(self, f: F) -> OrElseRecur<Self, E, F>
    where
        E: 'static + Decode<'b, Output = Self::Output>,
        F: 'static + Fn(RecurDecode<'b, Self::Output>) -> E,
        Self: Sized,
        Self: 'static,
    {
        OrElseRecur {
            base: self,
            f: f,
            __marker: PhantomData,
        }
    }

    #[inline]
    fn inverse(self) -> Inverse<Self>
    where
        Self: Sized,
    {
        Inverse { src: self }
    }
    #[inline]
    fn many_(self) -> Many_<Self>
    where
        Self: Sized,
    {
        Many_ { one: self }
    }
    #[inline]
    fn many(self) -> Many<Self>
    where
        Self: Sized,
    {
        Many { one: self }
    }
    #[inline]
    fn reduce_many<A, F>(self, f: F) -> ReduceMany<Self, A, F>
    where
        Self: Sized,
        A: Default,
        F: Fn(A, Self::Output) -> A,
    {
        ReduceMany {
            one: self,
            f,
            __marker: PhantomData,
        }
    }
    #[inline]
    fn repeat(self, n: u64) -> Repeat<Self>
    where
        Self: Sized,
    {
        Repeat { one: self, n }
    }
    #[inline]
    fn repeat_(self, n: u64) -> Repeat_<Self>
    where
        Self: Sized,
    {
        Repeat_ { one: self, n }
    }
    #[inline]
    fn reduce_repeat<A, F>(self, n: u64, f: F) -> ReduceRepeat<Self, A, F>
    where
        Self: Sized,
        A: Default,
        F: Fn(A, Self::Output) -> A,
    {
        ReduceRepeat {
            one: self,
            f,
            n,
            __marker: PhantomData,
        }
    }
}

#[derive(Copy, Clone)]
pub struct Void<D> {
    src: D,
}
impl<'b, D: Decode<'b>> Decode<'b> for Void<D> {
    type Output = ();

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], ()), DecodeError> {
        let (remainder, _) = self.src.decode(bytes)?;

        Ok((remainder, ()))
    }
}

#[derive(Copy, Clone)]
pub struct BytesConsumed<D> {
    src: D,
}
impl<'b, D: Decode<'b>> Decode<'b> for BytesConsumed<D> {
    type Output = usize;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], usize), DecodeError> {
        let total_len = bytes.len();
        let (remainder, _) = self.src.decode(bytes)?;

        Ok((remainder, total_len - remainder.len()))
    }
}

#[derive(Copy, Clone)]
pub struct Filter<D, F> {
    src: D,
    f: F,
}
impl<'b, D, F> Decode<'b> for Filter<D, F>
where
    D: Decode<'b>,
    F: Fn(&D::Output) -> bool,
{
    type Output = D::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let (remainder, x) = self.src.decode(bytes)?;
        let f = &self.f;

        if f(&x) {
            Ok((remainder, x))
        } else {
            Err(DecodeError::Fail)
        }
    }
}

// Functor
#[derive(Copy, Clone)]
pub struct Map<D, F> {
    src: D,
    f: F,
}

impl<'b, B, D: Decode<'b>, F> Decode<'b> for Map<D, F>
where
    F: Fn(D::Output) -> B,
{
    type Output = B;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], B), DecodeError> {
        let (remainder, x) = self.src.decode(bytes)?;
        let f = &self.f;

        Ok((remainder, f(x)))
    }
}

#[derive(Copy, Clone)]
pub struct FilterMap<D, F> {
    src: D,
    f: F,
}
impl<'b, T, D, F> Decode<'b> for FilterMap<D, F>
where
    D: Decode<'b>,
    F: Fn(D::Output) -> Option<T>,
{
    type Output = T;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], T), DecodeError> {
        let (remainder, r) = self.src.decode(bytes)?;
        let f = &self.f;

        match f(r) {
            Some(x) => Ok((remainder, x)),
            _ => Err(DecodeError::Fail),
        }
    }
}

#[derive(Copy, Clone)]
pub struct ToSlice<D> {
    src: D,
}
impl<'b, D: Decode<'b>> Decode<'b> for ToSlice<D> {
    type Output = &'b [u8];

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let total_len = bytes.len();
        let (remainder, _) = self.src.decode(bytes)?;
        let slice = &bytes[..(total_len - remainder.len())];

        Ok((remainder, slice))
    }
}

#[derive(Copy, Clone)]
pub struct ParseSlice<D, F> {
    src: D,
    f: F,
}
impl<'b, B, D: Decode<'b>, F> Decode<'b> for ParseSlice<D, F>
where
    F: Fn(&'b [u8]) -> B,
{
    type Output = B;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], B), DecodeError> {
        let total_len = bytes.len();
        let (remainder, _) = self.src.decode(bytes)?;
        let slice = &bytes[..(total_len - remainder.len())];
        let f = &self.f;

        Ok((remainder, f(slice)))
    }
}

// Monad
#[derive(Copy, Clone)]
pub struct FlatMap<D, F> {
    src: D,
    f: F,
}

impl<'b, B: Decode<'b>, D: Decode<'b>, F> Decode<'b> for FlatMap<D, F>
where
    F: Fn(D::Output) -> B,
{
    type Output = B::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], B::Output), DecodeError> {
        let (remainder, x) = self.src.decode(bytes)?;
        let f = &self.f;

        let next = f(x);
        let (next_remainder, o) = next.decode(remainder)?;
        Ok((next_remainder, o))
    }
}
#[derive(Copy, Clone)]
pub struct FlatMap_<D, F> {
    src: D,
    f: F,
}

impl<'b, B: Decode<'b>, D: Decode<'b>, F> Decode<'b> for FlatMap_<D, F>
where
    F: Fn(&D::Output) -> B,
{
    type Output = D::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], D::Output), DecodeError> {
        let (remainder, x) = self.src.decode(bytes)?;
        let f = &self.f;

        let next = f(&x);

        let (next_remainder, _) = next.decode(remainder)?;
        Ok((next_remainder, x))
    }
}

#[derive(Copy, Clone)]
pub struct AndNext<A, B> {
    fst: A,
    snd: B,
}
impl<'b, A: Decode<'b>, B: Decode<'b>> Decode<'b> for AndNext<A, B> {
    type Output = B::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let (remainder, _) = self.fst.decode(bytes)?;

        self.snd.decode(remainder)
    }
}
#[derive(Copy, Clone)]
pub struct AndNext_<A, B> {
    fst: A,
    snd: B,
}
impl<'b, A: Decode<'b>, B: Decode<'b>> Decode<'b> for AndNext_<A, B> {
    type Output = A::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let (remainder, fst_x) = self.fst.decode(bytes)?;

        let (remainder, _) = self.snd.decode(remainder)?;

        Ok((remainder, fst_x))
    }
}

// Alternative
#[derive(Copy, Clone)]
pub struct Alternative<A, B> {
    a: A,
    b: B,
}
impl<'b, A, B> Decode<'b> for Alternative<A, B>
where
    A: Decode<'b>,
    B: Decode<'b, Output = A::Output>,
{
    type Output = A::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], A::Output), DecodeError> {
        match self.a.decode(bytes) {
            Err(DecodeError::Fail) => self.b.decode(bytes),
            x @ _ => x,
        }
    }
}
#[derive(Copy, Clone)]
pub struct Inverse<D> {
    src: D,
}
impl<'b, D> Decode<'b> for Inverse<D>
where
    D: Decode<'b>,
{
    type Output = ();

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        match self.src.decode(bytes) {
            Err(DecodeError::Incomplete) => Err(DecodeError::Incomplete),
            Ok(_) => Err(DecodeError::Fail),
            _ => Ok((bytes, ())),
        }
    }
}

#[derive(Copy, Clone)]
pub struct Many_<D> {
    one: D,
}
impl<'b, D: Decode<'b>> Decode<'b> for Many_<D> {
    type Output = ();

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], ()), DecodeError> {
        let mut bytes = bytes;
        loop {
            match self.one.decode(bytes) {
                Ok((remainder, _)) => {
                    bytes = remainder;
                }
                _ => return Ok((bytes, ())),
            }
        }
    }
}
#[derive(Copy, Clone)]
pub struct Many<D> {
    one: D,
}
impl<'b, D: Decode<'b>> Decode<'b> for Many<D> {
    type Output = Vec<D::Output>;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Vec<D::Output>), DecodeError> {
        let mut results = vec![];
        let mut bytes = bytes;
        loop {
            match self.one.decode(bytes) {
                Ok((remainder, v)) => {
                    results.push(v);
                    bytes = remainder;
                }
                _ => return Ok((bytes, results)),
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct ReduceMany<D, A, F> {
    one: D,
    f: F,
    __marker: PhantomData<A>,
}
impl<'b, A, D, F> Decode<'b> for ReduceMany<D, A, F>
where
    D: Decode<'b>,
    F: Fn(A, D::Output) -> A,
    A: Default,
{
    type Output = A;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let mut result = A::default();
        let mut bytes = bytes;
        let f = &self.f;
        loop {
            match self.one.decode(bytes) {
                Ok((remainder, v)) => {
                    result = f(result, v);
                    bytes = remainder;
                }
                _ => return Ok((bytes, result)),
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct Repeat<D> {
    one: D,
    n: u64,
}
impl<'b, D: Decode<'b>> Decode<'b> for Repeat<D> {
    type Output = Vec<D::Output>;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Vec<D::Output>), DecodeError> {
        let mut results = vec![];
        let mut bytes = bytes;
        for _ in 0..self.n {
            match self.one.decode(bytes) {
                Ok((remainder, v)) => {
                    results.push(v);
                    bytes = remainder;
                }
                Err(DecodeError::Incomplete) => return Err(DecodeError::Incomplete),
                _ => return Err(DecodeError::Fail),
            }
        }
        Ok((bytes, results))
    }
}
#[derive(Copy, Clone)]
pub struct Repeat_<D> {
    one: D,
    n: u64,
}
impl<'b, D: Decode<'b>> Decode<'b> for Repeat_<D> {
    type Output = ();

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], ()), DecodeError> {
        let mut bytes = bytes;
        for _ in 0..self.n {
            match self.one.decode(bytes) {
                Ok((remainder, _)) => {
                    bytes = remainder;
                }
                Err(DecodeError::Incomplete) => return Err(DecodeError::Incomplete),
                _ => return Err(DecodeError::Fail),
            }
        }
        Ok((bytes, ()))
    }
}

#[derive(Copy, Clone)]
pub struct ReduceRepeat<D, A, F> {
    one: D,
    f: F,
    n: u64,
    __marker: PhantomData<A>,
}
impl<'b, A, D, F> Decode<'b> for ReduceRepeat<D, A, F>
where
    D: Decode<'b>,
    F: Fn(A, D::Output) -> A,
    A: Default,
{
    type Output = A;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let mut result = A::default();
        let mut bytes = bytes;
        let f = &self.f;
        for _ in 0..self.n {
            match self.one.decode(bytes) {
                Ok((remainder, v)) => {
                    result = f(result, v);
                    bytes = remainder;
                }
                Err(DecodeError::Incomplete) => return Err(DecodeError::Incomplete),
                _ => return Err(DecodeError::Fail),
            }
        }
        Ok((bytes, result))
    }
}

impl<'b, D> Decode<'b> for Box<D>
where
    D: Decode<'b> + ?Sized,
{
    type Output = D::Output;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        (**self).decode(bytes)
    }
}

impl<'b, O> Decode<'b> for fn(&'b [u8]) -> Result<(&'b [u8], O), DecodeError> {
    type Output = O;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        self(bytes)
    }
}

#[derive(Clone)]
pub struct RecurDecode<'b, O> {
    inner: Rc<Decode<'b, Output = O>>,
}

impl<'b, O> Decode<'b> for RecurDecode<'b, O> {
    type Output = O;

    #[inline]
    fn decode<'s>(&'s self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        self.inner.decode(bytes)
    }
}

#[derive(Copy, Clone)]
pub struct OrElseRecur<D, E, F> {
    base: D,
    f: F,
    __marker: PhantomData<E>,
}

impl<'b, D: 'static, E: 'static, F: 'static> Decode<'b> for OrElseRecur<D, E, F>
where
    D: Decode<'b>,
    E: Decode<'b, Output = D::Output>,
    F: Fn(RecurDecode<'b, D::Output>) -> E,
    Self: Clone,
{
    type Output = D::Output;

    #[inline]
    fn decode<'s>(&'s self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let recur = RecurDecode {
            inner: Rc::new(self.clone()),
        };
        let recur = (self.f)(recur);
        Self::decode_impl(&self.base, recur, bytes)
    }
}

impl<'b, D, E, F> OrElseRecur<D, E, F>
where
    D: Decode<'b>,
    E: Decode<'b, Output = D::Output>,
{
    #[inline]
    fn decode_impl(
        base: &D,
        recur: E,
        bytes: &'b [u8],
    ) -> Result<(&'b [u8], D::Output), DecodeError> {
        let result = base.decode(bytes);

        match result {
            x @ Ok(_) => return x,
            e @ Err(DecodeError::Incomplete) => return e,
            _ => {}
        }

        recur.decode(bytes)
    }
}
