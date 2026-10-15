#![no_std]

extern crate alloc;

pub struct PercentEncode<'a> {
    chunks: core::slice::Iter<'a, &'a str>,
}

impl<'a> PercentEncode<'a> {
    pub fn from_chunks(chunks: &'a [&'a str]) -> Self {
        Self { chunks: chunks.iter() }
    }
}

impl<'a> Iterator for PercentEncode<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().copied()
    }
}

#[path = "../../../../crate/src/encoder_cow.rs"]
mod encoder_cow;

pub fn convert<'a>(chunks: &'a [&'a str]) -> alloc::borrow::Cow<'a, str> {
    encoder_cow::into_cow(PercentEncode::from_chunks(chunks))
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::convert;
    use alloc::borrow::Cow;
    use alloc::string::String;

    #[test]
    fn ownership_cutoff_and_content() {
        assert_eq!(convert(&[]), Cow::Borrowed(""));
        assert_eq!(convert(&["%20"]), Cow::Borrowed("%20"));
        assert_eq!(convert(&["a", "%2F"]), Cow::<str>::Owned(String::from("a%2F")));
        assert_eq!(convert(&["a", "b", "c"]), Cow::<str>::Owned(String::from("abc")));
    }
}
