use std::{
    borrow::Cow,
    fmt::{Debug, Display},
};

use pest::{Parser, iterators::Pair};
use pest_derive::Parser;
use thiserror::Error;

mod imp;

#[derive(Parser)]
#[grammar = "rust_fmt.pest"] // relative to src
struct FmtParser;

#[derive(Debug)]
pub enum FmtType {
    Default,
    Debug,
    DebugLowHex,
    DebugUpHex,
    LowerHex,
    UpperHex,
    Octal,
    Ptr,
    Bin,
    LowExp,
    UpperExp,
}

impl Display for FmtType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FmtType::Default => Ok(()),
            FmtType::Debug => write!(f, "?"),
            FmtType::DebugLowHex => write!(f, "x?"),
            FmtType::DebugUpHex => write!(f, "X?"),
            FmtType::LowerHex => write!(f, "x"),
            FmtType::UpperHex => write!(f, "X"),
            FmtType::Octal => write!(f, "o"),
            FmtType::Ptr => write!(f, "p"),
            FmtType::Bin => write!(f, "b"),
            FmtType::LowExp => write!(f, "e"),
            FmtType::UpperExp => write!(f, "E"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Align {
    Left,
    Center,
    Right,
}

impl Display for Align {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Align::Center => write!(f, "^"),
            Align::Left => write!(f, "<"),
            Align::Right => write!(f, ">"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Sign {
    Positive,
    Negative,
}

impl Display for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sign::Positive => write!(f, "+"),
            Sign::Negative => write!(f, "-"),
        }
    }
}

#[derive(Debug)]
pub struct FormatSpec {
    pub fill: Option<char>,
    pub align: Option<Align>,
    pub sign: Option<Sign>,
    pub alternate: bool,
    pub zero: bool,
    pub width: Option<usize>,
    pub precision: Option<usize>,
    pub ty: FmtType,
}

impl Display for FormatSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.fill {
            write!(f, "{}", c)?;
        }
        if let Some(a) = self.align {
            write!(f, "{}", a)?;
        }
        if let Some(s) = self.sign {
            write!(f, "{}", s)?;
        }
        if self.alternate {
            write!(f, "#")?;
        }
        if self.zero {
            write!(f, "0")?;
        }
        if let Some(w) = self.width {
            write!(f, "{}", w)?;
        }
        if let Some(p) = self.precision {
            write!(f, ".{}", p)?;
        }
        write!(f, "{}", self.ty)
    }
}

impl Default for FormatSpec {
    fn default() -> Self {
        Self {
            fill: None,
            align: None,
            sign: None,
            alternate: false,
            zero: false,
            width: None,
            precision: None,
            ty: FmtType::Default,
        }
    }
}

impl FormatSpec {
    fn from_pair(p: Pair<'_, Rule>) -> Self {
        let mut out = Self::default();
        for p in p.into_inner() {
            match p.as_rule() {
                Rule::fill => out.fill = p.as_str().chars().nth(0),
                Rule::align => {
                    out.align = match p.as_str() {
                        "^" => Some(Align::Center),
                        "<" => Some(Align::Left),
                        ">" => Some(Align::Right),
                        _ => None,
                    }
                }
                Rule::sign => {
                    out.sign = match p.as_str() {
                        "-" => Some(Sign::Negative),
                        "+" => Some(Sign::Positive),
                        _ => None,
                    }
                }
                Rule::alternate => out.alternate = true,
                Rule::zero_pad => out.zero = true,
                Rule::width => out.width = p.as_str().parse::<usize>().ok(),
                Rule::precision => out.precision = p.as_str().parse::<usize>().ok(),
                Rule::type_fmt => {
                    if let Some(type_fmt) = p.into_inner().next() {
                        match type_fmt.as_rule() {
                            Rule::type_debug => out.ty = FmtType::Debug,
                            Rule::type_debug_low_hex => out.ty = FmtType::DebugLowHex,
                            Rule::type_debug_up_hex => out.ty = FmtType::DebugUpHex,
                            Rule::type_oct => out.ty = FmtType::Octal,
                            Rule::type_low_hex => out.ty = FmtType::LowerHex,
                            Rule::type_up_hex => out.ty = FmtType::UpperHex,
                            Rule::type_ptr => out.ty = FmtType::Ptr,
                            Rule::type_bin => out.ty = FmtType::Bin,
                            Rule::type_low_exp => out.ty = FmtType::LowExp,
                            Rule::type_upper_exp => out.ty = FmtType::UpperExp,
                            _ => {}
                        }
                    }
                }

                _ => {}
            }
        }
        out
    }

    fn is_empty(&self) -> bool {
        self.fill.is_none()
            && self.align.is_none()
            && self.sign.is_none()
            && !self.alternate
            && !self.zero
            && self.width.is_none()
            && self.precision.is_none()
            && matches!(self.ty, FmtType::Default)
    }

    pub fn fill_and_align(&self, s: String, default_align: Align) -> String {
        let width = self.width.unwrap_or(s.len());
        if width <= s.len() {
            s
        } else {
            let mut out = String::new();
            let pad = width.saturating_sub(s.len());
            let align = self.align.unwrap_or(default_align);
            match align {
                Align::Left => {
                    out.push_str(&s);
                    (0..pad).for_each(|_| out.push(self.fill.unwrap_or(' ')));
                }
                Align::Center => {
                    if pad > 0 {
                        let r_pad = pad / 2;
                        let l_pad = pad.div_ceil(2);
                        (0..r_pad).for_each(|_| out.push(self.fill.unwrap_or(' ')));
                        out.push_str(&s);
                        (0..l_pad).for_each(|_| out.push(self.fill.unwrap_or(' ')));
                    }
                }
                Align::Right => {
                    (0..pad).for_each(|_| out.push(self.fill.unwrap_or(' ')));
                    out.push_str(&s);
                }
            }
            out
        }
    }
}

#[derive(Debug)]
struct Format {
    start: usize,
    end: usize,
    arg: Option<String>,
    spec: FormatSpec,
}

impl Display for Format {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        if let Some(a) = self.arg.as_ref() {
            write!(f, "{}", a)?;
        }

        if !self.spec.is_empty() {
            write!(f, ":")?;
        }
        write!(f, "{}", self.spec)?;
        write!(f, "}}")
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("unsupported format spec")]
    UnsupportedSpec,
    #[error("format strings don't match with number of arguments")]
    FormatVsArgs,
    #[error("unknown parsing rule={0}")]
    UnknownParsingRule(String),
    #[error("format parsing error: {0}")]
    Parse(#[from] Box<pest::error::Error<Rule>>),
}

pub trait DynDisplay {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error>;
}

impl Format {
    fn from_pair(pairs: Pair<'_, Rule>) -> Self {
        let start = pairs.as_span().start();
        let end = pairs.as_span().end();
        let mut spec = None;
        let mut arg = None;

        for p in pairs.into_inner() {
            match p.as_rule() {
                Rule::argument => {
                    // we ignore it for the moment
                    arg = Some(p.as_str().to_string())
                }
                Rule::format_spec => spec = Some(FormatSpec::from_pair(p)),
                _ => {}
            }
        }

        Self {
            start,
            end,
            arg,
            spec: spec.unwrap_or_default(),
        }
    }

    fn dyn_fmt_arg<D: DynDisplay>(&self, arg: &D) -> Result<String, Error> {
        DynDisplay::dyn_fmt(arg, &self.spec)
    }
}

#[derive(Debug)]
pub struct FormatString {
    s: String,
    fmts: Vec<Format>,
}

impl FormatString {
    #[inline]
    fn new_from_str<S: AsRef<str>>(s: S) -> Result<Self, Error> {
        let pairs = FmtParser::parse(Rule::format_string, s.as_ref())
            .map_err(|e| Error::from(Box::new(e)))?;

        let mut fmts = vec![];

        for p in pairs {
            // WARNING: here anything else than Rule::format is ignored
            if p.as_rule() == Rule::format {
                fmts.push(Format::from_pair(p))
            }
        }

        Ok(Self {
            s: s.as_ref().to_string(),
            fmts,
        })
    }

    pub fn from_string(s: String) -> Result<Self, Error> {
        Self::new_from_str(s)
    }

    pub fn into_string(self) -> String {
        self.s
    }

    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        Cow::Borrowed(&self.s)
    }

    pub fn contains_format(&self) -> bool {
        !self.fmts.is_empty()
    }
}

pub struct Formatter<'s> {
    /// index in the format string
    i: usize,
    /// index of of the format string argument
    i_arg: usize,
    format_string: &'s FormatString,
    out: String,
}

impl<'s> From<&'s FormatString> for Formatter<'s> {
    fn from(value: &'s FormatString) -> Self {
        Self {
            i: 0,
            i_arg: 0,
            format_string: value,
            out: String::new(),
        }
    }
}

impl Formatter<'_> {
    pub fn format_arg<A: DynDisplay>(&mut self, arg: &A) -> Result<&mut Self, Error> {
        let Some(arg_fmt) = &self.format_string.fmts.get(self.i_arg) else {
            return Ok(self);
        };

        let slice = &self.format_string.s.as_str()[self.i..];
        self.out.push_str(&slice[..arg_fmt.start - self.i]);
        self.out.push_str(&arg_fmt.dyn_fmt_arg(arg)?);
        self.i = arg_fmt.end;
        self.i_arg += 1;

        Ok(self)
    }

    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        Cow::Borrowed(&self.out)
    }

    pub fn into_string(self) -> String {
        self.out
    }
}

#[macro_export]
macro_rules! dformat {
    ($fmt: expr, $($arg: expr),*) => {
        {
            let mut last_err = None;
            let mut fs = $crate::Formatter::from($fmt);
            $(
                if let Err(e)=fs.format_arg(&$arg) {
                    last_err = Some(e);
                }
            )*
            match last_err {
                Some(e) => Err(e),
                None => Ok(fs.into_string()),
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use std::{
        ffi::{OsStr, OsString},
        net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
        path::{Path, PathBuf},
        rc::Rc,
        sync::Arc,
        time::{Duration, Instant, SystemTime},
    };

    use pest::Parser;

    use super::*;

    macro_rules! dformat_lit {
        ($fmt: literal, $($arg: expr),*) => {
            {
                let fs = FormatString::new_from_str($fmt).unwrap();
                dformat!(&fs, $($arg),*)
            }
        };
    }

    #[test]
    fn test_rule_format() {
        for f in [
            "{}", "{0}", "{name}", "{:>5}", "{:<5}", "{:^5}", "{:05}", "{:+}", "{:-}", "{:#b}",
            "{:#o}", "{:#x}", "{:.2}", "{:08.2}", "{:x}", "{:X}", "{:o}", "{:b}", "{:e}", "{:E}",
            "{:?}", "{:#?}", "{:p}",
        ] {
            let fmt = Format::from_pair(
                FmtParser::parse(Rule::format, f)
                    .inspect_err(|e| println!("{}", e))
                    .unwrap()
                    .next()
                    .unwrap(),
            );

            assert_eq!(f, format!("{}", fmt));
        }
    }

    #[test]
    fn test_integer_formatting() {
        // Decimal formatting
        assert_eq!(format!("{}", 42), dformat_lit!("{}", 42).unwrap());
        assert_eq!(format!("{:5}", 42), dformat_lit!("{:5}", 42).unwrap());
        assert_eq!(format!("{:05}", 42), dformat_lit!("{:05}", 42).unwrap());
        assert_eq!(format!("{:+}", 42), dformat_lit!("{:+}", 42).unwrap());
        assert_eq!(format!("{: }", 42), dformat_lit!("{: }", 42).unwrap());
        assert_eq!(format!("{:#}", 42), dformat_lit!("{:#}", 42).unwrap());

        // Hexadecimal formatting
        assert_eq!(format!("{:x}", 42), dformat_lit!("{:x}", 42).unwrap());
        assert_eq!(format!("{:X}", 42), dformat_lit!("{:X}", 42).unwrap());
        assert_eq!(format!("{:#x}", 42), dformat_lit!("{:#x}", 42).unwrap());
        assert_eq!(format!("{:#X}", 42), dformat_lit!("{:#X}", 42).unwrap());

        // Octal formatting
        assert_eq!(format!("{:o}", 42), dformat_lit!("{:o}", 42).unwrap());
        assert_eq!(format!("{:#o}", 42), dformat_lit!("{:#o}", 42).unwrap());

        // Binary formatting
        assert_eq!(format!("{:b}", 42), dformat_lit!("{:b}", 42).unwrap());
        assert_eq!(format!("{:#b}", 42), dformat_lit!("{:#b}", 42).unwrap());

        // Width and alignment
        assert_eq!(format!("{:5}", 42), dformat_lit!("{:5}", 42).unwrap());
        assert_eq!(format!("{:<5}", 42), dformat_lit!("{:<5}", 42).unwrap());
        assert_eq!(format!("{:>5}", 42), dformat_lit!("{:>5}", 42).unwrap());
        assert_eq!(format!("{:^5}", 42), dformat_lit!("{:^5}", 42).unwrap());
        assert_eq!(format!("{:05}", 42), dformat_lit!("{:05}", 42).unwrap());
        assert_eq!(format!("{:+<5}", 42), dformat_lit!("{:+<5}", 42).unwrap());
        assert_eq!(format!("{:->5}", 42), dformat_lit!("{:->5}", 42).unwrap());
        assert_eq!(format!("{:+^5}", 42), dformat_lit!("{:+^5}", 42).unwrap());
    }

    #[test]
    fn test_float_formatting() {
        // Float formatting
        assert_eq!(format!("{}", 42.0), dformat_lit!("{}", 42.0).unwrap());
        assert_eq!(format!("{:e}", 42.0), dformat_lit!("{:e}", 42.0).unwrap());
        assert_eq!(format!("{:E}", 42.0), dformat_lit!("{:E}", 42.0).unwrap());
        assert_eq!(format!("{:.2}", 42.0), dformat_lit!("{:.2}", 42.0).unwrap());
        assert_eq!(
            format!("{:.2}", 42.1234),
            dformat_lit!("{:.2}", 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:10.2}", 42.1234),
            dformat_lit!("{:10.2}", 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:<10.2}", 42.1234),
            dformat_lit!("{:<10.2}", 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:>10.2}", 42.1234),
            dformat_lit!("{:>10.2}", 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:^10.2}", 42.1234),
            dformat_lit!("{:^10.2}", 42.1234).unwrap()
        );
        assert_eq!(format!("{:+}", 42.0), dformat_lit!("{:+}", 42.0).unwrap());
        assert_eq!(
            format!("{:+<10.2}", 42.1234),
            dformat_lit!("{:+<10.2}", 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:->10.2}", 42.1234),
            dformat_lit!("{:->10.2}", 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:+^10.2}", 42.1234),
            dformat_lit!("{:+^10.2}", 42.1234).unwrap()
        );
    }

    #[test]
    fn test_string_formatting() {
        // String formatting
        assert_eq!(format!("{}", "hello"), dformat_lit!("{}", "hello").unwrap());
        assert_eq!(
            format!("{:10}", "hello"),
            dformat_lit!("{:10}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:<10}", "hello"),
            dformat_lit!("{:<10}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:>10}", "hello"),
            dformat_lit!("{:>10}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:^10}", "hello"),
            dformat_lit!("{:^10}", "hello").unwrap()
        );

        // String precision
        assert_eq!(
            format!("{:.3}", "hello"),
            dformat_lit!("{:.3}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:10.3}", "hello"),
            dformat_lit!("{:10.3}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:<10.3}", "hello"),
            dformat_lit!("{:<10.3}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:>10.3}", "hello"),
            dformat_lit!("{:>10.3}", "hello").unwrap()
        );
        assert_eq!(
            format!("{:^10.3}", "hello"),
            dformat_lit!("{:^10.3}", "hello").unwrap()
        );
    }

    #[test]
    fn test_char_formatting() {
        // Character formatting
        assert_eq!(format!("{}", 'A'), dformat_lit!("{}", 'A').unwrap());
        assert_eq!(format!("{:5}", 'A'), dformat_lit!("{:5}", 'A').unwrap());
        assert_eq!(format!("{:<5}", 'A'), dformat_lit!("{:<5}", 'A').unwrap());
        assert_eq!(format!("{:>5}", 'A'), dformat_lit!("{:>5}", 'A').unwrap());
        assert_eq!(format!("{:^5}", 'A'), dformat_lit!("{:^5}", 'A').unwrap());
    }

    #[test]
    fn test_bool_formatting() {
        // Boolean formatting
        assert_eq!(format!("{}", true), dformat_lit!("{}", true).unwrap());
        assert_eq!(format!("{}", false), dformat_lit!("{}", false).unwrap());
        assert_eq!(format!("{:5}", true), dformat_lit!("{:5}", true).unwrap());
        assert_eq!(format!("{:<5}", true), dformat_lit!("{:<5}", true).unwrap());
        assert_eq!(format!("{:>5}", true), dformat_lit!("{:>5}", true).unwrap());
        assert_eq!(format!("{:^5}", true), dformat_lit!("{:^5}", true).unwrap());
    }

    #[test]
    fn test_pointer_formatting() {
        // Pointer formatting
        let x = 42;
        let ptr = &x as *const i32;
        assert_eq!(format!("{:p}", ptr), dformat_lit!("{:p}", ptr).unwrap());
        assert_eq!(format!("{:10p}", ptr), dformat_lit!("{:10p}", ptr).unwrap());
        assert_eq!(
            format!("{:<10p}", ptr),
            dformat_lit!("{:<10p}", ptr).unwrap()
        );
        assert_eq!(
            format!("{:>10p}", ptr),
            dformat_lit!("{:>10p}", ptr).unwrap()
        );
        assert_eq!(
            format!("{:^10p}", ptr),
            dformat_lit!("{:^10p}", ptr).unwrap()
        );
    }

    #[test]
    fn test_multiple_arguments() {
        // Multiple arguments
        assert_eq!(
            format!("{} {}", "hello", 42),
            dformat_lit!("{} {}", "hello", 42).unwrap()
        );
        assert_eq!(
            format!("{:5} {:<10.2}", 42, 42.1234),
            dformat_lit!("{:5} {:<10.2}", 42, 42.1234).unwrap()
        );
        assert_eq!(
            format!("{:>5} {:^10.2}", 42, 42.1234),
            dformat_lit!("{:>5} {:^10.2}", 42, 42.1234).unwrap()
        );
    }

    #[test]
    fn test_complex_formatting() {
        // Complex formatting
        assert_eq!(
            format!("{:05} {:<10.2} {:^10}", 42, 42.1234, "hello"),
            dformat_lit!("{:05} {:<10.2} {:^10}", 42, 42.1234, "hello").unwrap()
        );
        assert_eq!(
            format!("{:+<5} {:^10.2} {:>10}", 42, 42.1234, "hello"),
            dformat_lit!("{:+<5} {:^10.2} {:>10}", 42, 42.1234, "hello").unwrap()
        );
    }

    #[test]
    fn test_network_types() {
        // IpAddr, Ipv4Addr, Ipv6Addr
        let ipv4_addr = Ipv4Addr::new(127, 0, 0, 1);
        let ipv6_addr = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1);
        let ip_addr_v4 = IpAddr::V4(ipv4_addr);
        let ip_addr_v6 = IpAddr::V6(ipv6_addr);

        assert_eq!(
            format!("{}", ipv4_addr),
            dformat_lit!("{}", ipv4_addr).unwrap()
        );
        assert_eq!(
            format!("{:?}", ipv4_addr),
            dformat_lit!("{:?}", ipv4_addr).unwrap()
        );
        assert_eq!(
            format!("{}", ipv6_addr),
            dformat_lit!("{}", ipv6_addr).unwrap()
        );
        assert_eq!(
            format!("{:?}", ipv6_addr),
            dformat_lit!("{:?}", ipv6_addr).unwrap()
        );
        assert_eq!(
            format!("{}", ip_addr_v4),
            dformat_lit!("{}", ip_addr_v4).unwrap()
        );
        assert_eq!(
            format!("{:?}", ip_addr_v4),
            dformat_lit!("{:?}", ip_addr_v4).unwrap()
        );
        assert_eq!(
            format!("{}", ip_addr_v6),
            dformat_lit!("{}", ip_addr_v6).unwrap()
        );
        assert_eq!(
            format!("{:?}", ip_addr_v6),
            dformat_lit!("{:?}", ip_addr_v6).unwrap()
        );

        // SocketAddr, SocketAddrV4, SocketAddrV6
        let socket_addr_v4 = SocketAddrV4::new(ipv4_addr, 8080);
        let socket_addr_v6 = SocketAddrV6::new(ipv6_addr, 8080, 0, 0);
        let socket_addr = SocketAddr::V4(socket_addr_v4);

        assert_eq!(
            format!("{}", socket_addr_v4),
            dformat_lit!("{}", socket_addr_v4).unwrap()
        );
        assert_eq!(
            format!("{:?}", socket_addr_v4),
            dformat_lit!("{:?}", socket_addr_v4).unwrap()
        );
        assert_eq!(
            format!("{}", socket_addr_v6),
            dformat_lit!("{}", socket_addr_v6).unwrap()
        );
        assert_eq!(
            format!("{:?}", socket_addr_v6),
            dformat_lit!("{:?}", socket_addr_v6).unwrap()
        );
        assert_eq!(
            format!("{}", socket_addr),
            dformat_lit!("{}", socket_addr).unwrap()
        );
        assert_eq!(
            format!("{:?}", socket_addr),
            dformat_lit!("{:?}", socket_addr).unwrap()
        );
    }

    #[test]
    fn test_time_types() {
        // Duration, SystemTime, Instant
        let duration = Duration::from_secs(3600);
        let system_time = SystemTime::now();
        let instant = Instant::now();

        assert_eq!(
            format!("{:?}", duration),
            dformat_lit!("{:?}", duration).unwrap()
        );
        assert_eq!(
            format!("{:?}", system_time),
            dformat_lit!("{:?}", system_time).unwrap()
        );
        assert_eq!(
            format!("{:?}", instant),
            dformat_lit!("{:?}", instant).unwrap()
        );
    }

    #[test]
    fn test_path_types() {
        // Path, PathBuf
        let path = Path::new("/path/to/file");
        let path_buf = PathBuf::from("/path/to/file");

        assert_eq!(format!("{:?}", path), dformat_lit!("{:?}", path).unwrap());
        assert_eq!(
            format!("{:?}", path_buf),
            dformat_lit!("{:?}", path_buf).unwrap()
        );
    }

    #[test]
    fn test_ffi_types() {
        // OsString, OsStr
        let os_string = OsString::from("OS String");
        let os_str: &OsStr = os_string.as_os_str();

        assert_eq!(
            format!("{:?}", os_string),
            dformat_lit!("{:?}", os_string).unwrap()
        );
        assert_eq!(
            format!("{:?}", os_str),
            dformat_lit!("{:?}", os_str).unwrap()
        );
    }

    #[test]
    fn test_smart_pointers() {
        // Box, Rc, Arc, Cow
        let boxed = Box::new(42);
        let rc = Rc::new(42);
        let arc = Arc::new(42);
        let cow_str: Cow<'_, str> = Cow::Borrowed("Hello");

        assert_eq!(format!("{}", boxed), dformat_lit!("{}", boxed).unwrap());
        assert_eq!(format!("{}", rc), dformat_lit!("{}", rc).unwrap());
        assert_eq!(format!("{}", arc), dformat_lit!("{}", arc).unwrap());
        assert_eq!(format!("{}", cow_str), dformat_lit!("{}", cow_str).unwrap());
    }
}
