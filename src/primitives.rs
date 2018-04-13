use super::decode::{Decode, DecodeError};

#[derive(Debug, Copy, Clone)]
pub struct Byte(u8);

impl Byte {
    pub fn new(b: u8) -> Byte {
        Byte(b)
    }
}
impl<'b> Decode<'b> for Byte {
    type Output = u8;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], u8), DecodeError> {
        if bytes.len() == 0 {
            return Err(DecodeError::Incomplete);
        }

        if bytes[0] == self.0 {
            Ok((&bytes[1..], self.0))
        } else {
            Err(DecodeError::Fail)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ByteAny;

impl<'b> Decode<'b> for ByteAny {
    type Output = u8;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        if bytes.len() == 0 {
            Err(DecodeError::Incomplete)
        } else {
            Ok((&bytes[1..], bytes[0]))
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ByteLineSafe;

impl<'b> Decode<'b> for ByteLineSafe {
    type Output = u8;

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        if bytes.len() == 0 {
            return Err(DecodeError::Incomplete);
        }

        let b = bytes[0];

        match b {
            b'\r' => Err(DecodeError::Fail),
            b'\n' => Err(DecodeError::Fail),
            _ => Ok((&bytes[1..], b)),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct BytesExact {
    bytes: &'static [u8],
}
impl BytesExact {
    pub fn new(bytes: &'static [u8]) -> Self {
        BytesExact { bytes }
    }
}

impl<'b> Decode<'b> for BytesExact {
    type Output = &'static [u8];

    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let expected_bytes = self.bytes;
        let expected_len = expected_bytes.len();
        if bytes.len() < expected_len {
            return Err(DecodeError::Incomplete);
        }

        if &bytes[0..expected_len] == expected_bytes {
            Ok((&bytes[expected_len..], self.bytes))
        } else {
            Err(DecodeError::Fail)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct BytesFixedLen {
    size: usize,
}

impl BytesFixedLen {
    pub fn new(size: usize) -> Self {
        BytesFixedLen { size }
    }
}

impl<'b> Decode<'b> for BytesFixedLen {
    type Output = &'b [u8];
    #[inline]
    fn decode<'a>(&'a self, bytes: &'b [u8]) -> Result<(&'b [u8], Self::Output), DecodeError> {
        let n = self.size;
        if bytes.len() < n {
            Err(DecodeError::Incomplete)
        } else {
            Ok((&bytes[n..], &bytes[0..n]))
        }
    }
}
