use std::{
    borrow::Cow,
    fmt::{Debug, Display},
};

use pest::{Parser, iterators::Pair};
use pest_derive::Parser;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "rust_fmt.pest"] // relative to src
struct FmtParser;

#[derive(Debug)]
pub enum FmtType {
    Unsupported,
    Default,
    LowerHex,
    UpperHex,
    Octal,
    Ptr,
    Bin,
    LowExp,
    UpperExp,
}

#[derive(Debug)]
struct Format<'s> {
    fmt: Cow<'s, str>,
    ty: FmtType,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("unsupported format")]
    UnsupportedFormat,
    #[error("format strings don't match with number of arguments")]
    FormatVsArgs,
}

pub trait DynDisplay: Display + Debug {
    fn fmt(&self, t: &FmtType) -> Result<String, Error>;
}

macro_rules! impl_dyn_display_int {
    ($ty: ty) => {
        impl DynDisplay for $ty {
            #[inline]
            fn fmt(&self, t: &FmtType) -> Result<String, Error> {
                match t {
                    FmtType::Default => Ok(format!("{}", self)),
                    FmtType::LowerHex => Ok(format!("{:x}", self)),
                    FmtType::UpperHex => Ok(format!("{:X}", self)),
                    FmtType::Bin => Ok(format!("{:b}", self)),
                    FmtType::Ptr => Ok(format!("{:p}", self)),
                    FmtType::Octal => Ok(format!("{:o}", self)),
                    FmtType::LowExp => Ok(format!("{:e}", self)),
                    FmtType::UpperExp => Ok(format!("{:e}", self)),
                    _ => Err(Error::UnsupportedFormat),
                }
            }
        }
    };
}

impl<T: DynDisplay> DynDisplay for Box<T> {
    fn fmt(&self, t: &FmtType) -> Result<String, Error> {
        DynDisplay::fmt(self.as_ref(), t)
    }
}

// Signed integers
impl_dyn_display_int!(i8);
impl_dyn_display_int!(i16);
impl_dyn_display_int!(i32);
impl_dyn_display_int!(i64);
impl_dyn_display_int!(i128);
impl_dyn_display_int!(isize);

// Unsigned integers
impl_dyn_display_int!(u8);
impl_dyn_display_int!(u16);
impl_dyn_display_int!(u32);
impl_dyn_display_int!(u64);
impl_dyn_display_int!(u128);
impl_dyn_display_int!(usize);

impl<'s> Format<'s> {
    fn from_pair(pairs: Pair<'s, Rule>) -> Self {
        let ty = match pairs.as_str() {
            "{}" => FmtType::Default,
            "{:x}" => FmtType::LowerHex,
            "{:X}" => FmtType::UpperHex,
            "{:o}" => FmtType::Octal,
            "{:b}" => FmtType::Bin,
            "{:p}" => FmtType::Ptr,
            "{:e}" => FmtType::LowExp,
            "{:E}" => FmtType::UpperExp,

            _ => FmtType::Unsupported,
        };

        Self {
            fmt: Cow::Borrowed(pairs.as_str()),
            ty,
        }
    }

    fn fmt<D: DynDisplay>(&self, v: &D) -> Result<String, Error> {
        DynDisplay::fmt(v, &self.ty)
    }
}

#[derive(Debug)]
pub struct FormatString<'s> {
    s: Cow<'s, str>,
    fmts: Vec<Format<'s>>,
}

impl<'s> FormatString<'s> {
    pub fn parse(s: &'s str) -> Self {
        //FIXME: remove unwrap
        let pairs = FmtParser::parse(Rule::format_string, s)
            .inspect_err(|e| println!("{}", e))
            .unwrap();

        let mut fmts = vec![];

        for p in pairs {
            match p.as_rule() {
                Rule::format => fmts.push(Format::from_pair(p)),
                Rule::EOI => {}
                _ => {
                    //FIXME: return Error instead
                    unimplemented!()
                }
            }
        }

        Self {
            s: Cow::Borrowed(s),
            fmts,
        }
    }

    pub fn is_format_string(&self) -> bool {
        !self.fmts.is_empty()
    }
}

pub struct Formatter<'s> {
    i: usize,
    i_arg: usize,
    format_string: &'s FormatString<'s>,
    out: String,
}

impl<'s> From<&'s FormatString<'s>> for Formatter<'s> {
    fn from(value: &'s FormatString<'s>) -> Self {
        Self {
            i: 0,
            i_arg: 0,
            format_string: value,
            out: String::new(),
        }
    }
}

impl Formatter<'_> {
    pub fn format_arg<A: DynDisplay>(&mut self, arg: &A) -> &mut Self {
        let slice = &self.format_string.s[self.i..];
        let arg_fmt = &self.format_string.fmts[self.i_arg];
        let arg_i = slice.find(arg_fmt.fmt.as_ref()).unwrap();
        self.out.push_str(&slice[..arg_i]);
        self.out.push_str(&arg_fmt.fmt(arg).unwrap());
        self.i += arg_i + arg_fmt.fmt.len();
        self.i_arg += 1;
        self
    }

    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        Cow::Borrowed(&self.out)
    }
}

#[macro_export]
macro_rules! dformat {
    (&$fmt: expr, $($arg: expr),*) => {
        {
            let mut fs = $crate::Formatter::from(&$fmt);
            $(
                fs.format_arg(&$arg);
            )*
            fs.to_string_lossy().to_string()
        }
    };
    ($fmt: expr, $($arg: expr),*) => {
        dformat!(&$fmt, $($arg),*)
    };
}

#[cfg(test)]
mod tests {
    use pest::Parser;

    use super::*;

    #[test]
    fn test_rule_format() {
        for f in [
            "{}", "{0}", "{name}", "{:>5}", "{:<5}", "{:^5}", "{:05}", "{:+}", "{:-}", "{: }",
            "{:#b}", "{:#o}", "{:#x}", "{:.2}", "{:08.2}", "{:x}", "{:X}", "{:o}", "{:b}", "{:e}",
            "{:E}", "{:?}", "{:#?}", "{:p}",
        ] {
            FmtParser::parse(Rule::format, f)
                .inspect_err(|e| println!("{}", e))
                .unwrap();
        }
    }

    #[test]
    fn test_rule_format_string() {
        for f in [
            "Default format: {}",
            "Positional args: {0}, {1}, {2}",
            "Named args: {num}, {float}",
            "Right-aligned: {:>5}",
            "Left-aligned: {:<5}",
            "Centered: {:^5}",
            "Zero-padded: {:05}",
            "Always show sign: {:+}",
            "Show negative sign only: {:-}",
            "Show space for positive numbers: {: }",
            "Binary with prefix: {:#b}",
            "Octal with prefix: {:#o}",
            "Hex with prefix: {:#x}",
            "Floating-point precision: {:.2}",
            "Zero-padded floating-point: {:08.2}",
            "Lowercase hex: {:x}",
            "Uppercase hex: {:X}",
            "Octal: {:o}",
            "Binary: {:b}",
            "Scientific notation (e): {:e}",
            "Scientific notation (E): {:E}",
            "Debug format: {:?}",
            "Pretty-print debug format: {:#?}",
            "Pointer address: {:p}",
        ]
        .iter()
        {
            let mut pairs = FmtParser::parse(Rule::format_string, f)
                .inspect_err(|e| println!("{}", e))
                .unwrap();
            println!("{:?}", pairs.next().unwrap().as_rule());
            println!("{:?}", FormatString::parse(f));
        }
    }

    #[test]
    fn test_dyn_display() {
        let f = FormatString::parse("this is a test: 0x{:x}");
        let mut fs = Formatter::from(&f);
        fs.format_arg(&b'A');
        println!("{}", fs.to_string_lossy());
    }

    #[test]
    fn test_macro() {
        let s = FormatString::parse("test 0x{:x} {} {:x}");
        assert_eq!(dformat!(&s, 0x42, 43, b'A'), "test 0x42 43 41");
        assert_eq!(dformat!(s, 0x42, 43, b'A'), "test 0x42 43 41");
    }
}
