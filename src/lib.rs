#![deny(unused_imports)]
#![deny(missing_docs)]
//! # Dynamic String Formatting for Rust
//!
//! The `dyf` crate brings dynamic string formatting to Rust while supporting the whole variety of string formats available in Rust.
//! It provides an easy way to implement dynamic formatting for custom types with the implementation of the `DynDisplay` trait.
//!
//! ## Features
//!
//! - Support for all standard Rust format specifiers
//! - Dynamic formatting for custom types via the `DynDisplay` trait
//! - Macro support for convenient usage
//! - Support for various standard library types
//!
//! ## Usage
//!
//! Add the crate to your project:
//!
//! ```sh
//! cargo add dyf
//! ```
//!
//! ## Examples
//!
//! ### Basic Formatting
//!
//! ```rust
//! use dyf::{dformat, FormatString};
//!
//! let fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
//! let result = dformat!(&fmt, "world").unwrap();
//! assert_eq!(result, format!("Hello, {}!", "world"));
//!
//! let num_fmt = FormatString::from_string("The answer is: {:>5}".to_string()).unwrap();
//! let num = 42;
//! let result = dformat!(&num_fmt, num).unwrap();
//! assert_eq!(result, format!("The answer is: {:>5}", num));
//! ```
//!
//! ### Advanced Formatting
//!
//! ```rust
//! use dyf::{dformat, FormatString};
//!
//! let fmt = FormatString::from_string("{:05} {:<10.2} {:^10}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42, 42.1234, "hello").unwrap();
//! assert_eq!(result, format!("{:05} {:<10.2} {:^10}", 42, 42.1234, "hello"));
//! ```
//!
//! ### Custom Type Formatting
//!
//! ```rust
//! use dyf::{DynDisplay, Error, FormatSpec, dformat, FormatString};
//!
//! struct Point {
//!     x: i32,
//!     y: i32,
//! }
//!
//! impl DynDisplay for Point {
//!     fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
//!         Ok(format!("Point({}, {})", self.x, self.y))
//!     }
//! }
//!
//! impl std::fmt::Display for Point {
//!     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//!         write!(f, "Point({}, {})", self.x, self.y)
//!     }
//! }
//!
//! let point = Point { x: 10, y: 20 };
//! let fmt = FormatString::from_string("{}".to_string()).unwrap();
//! let result = dformat!(&fmt, point).unwrap();
//! assert_eq!(result, format!("{}", point));
//! ```
//!
//! ### Integer Formatting
//!
//! ```rust
//! use dyf::{dformat, FormatString};
//!
//! // Decimal formatting
//! let fmt = FormatString::from_string("{}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{}", 42));
//!
//! let fmt = FormatString::from_string("{:5}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:5}", 42));
//!
//! let fmt = FormatString::from_string("{:05}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:05}", 42));
//!
//! let fmt = FormatString::from_string("{:+}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:+}", 42));
//!
//! // Hexadecimal formatting
//! let fmt = FormatString::from_string("{:x}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:x}", 42));
//!
//! let fmt = FormatString::from_string("{:X}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:X}", 42));
//!
//! // Octal formatting
//! let fmt = FormatString::from_string("{:o}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:o}", 42));
//!
//! // Binary formatting
//! let fmt = FormatString::from_string("{:b}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42).unwrap();
//! assert_eq!(result, format!("{:b}", 42));
//! ```
//!
//! ### Float Formatting
//!
//! ```rust
//! use dyf::{dformat, FormatString};
//!
//! let fmt = FormatString::from_string("{}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42.0).unwrap();
//! assert_eq!(result, format!("{}", 42.0));
//!
//! let fmt = FormatString::from_string("{:e}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42.0).unwrap();
//! assert_eq!(result, format!("{:e}", 42.0));
//!
//! let fmt = FormatString::from_string("{:.2}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42.1234).unwrap();
//! assert_eq!(result, format!("{:.2}", 42.1234));
//!
//! let fmt = FormatString::from_string("{:10.2}".to_string()).unwrap();
//! let result = dformat!(&fmt, 42.1234).unwrap();
//! assert_eq!(result, format!("{:10.2}", 42.1234));
//! ```
//!
//! ### String Formatting
//!
//! ```rust
//! use dyf::{dformat, FormatString};
//!
//! let fmt = FormatString::from_string("{}".to_string()).unwrap();
//! let result = dformat!(&fmt, "hello").unwrap();
//! assert_eq!(result, format!("{}", "hello"));
//!
//! let fmt = FormatString::from_string("{:10}".to_string()).unwrap();
//! let result = dformat!(&fmt, "hello").unwrap();
//! assert_eq!(result, format!("{:10}", "hello"));
//!
//! let fmt = FormatString::from_string("{:.3}".to_string()).unwrap();
//! let result = dformat!(&fmt, "hello").unwrap();
//! assert_eq!(result, format!("{:.3}", "hello"));
//! ```
//!
//! ## Supported Format Specifiers
//!
//! The crate supports all standard Rust format specifiers, including:
//!
//! | Category | Specifiers |
//! |----------|------------|
//! | Fill/Alignment | `<` `>` `^` |
//! | Sign | `+` `-` |
//! | Alternate | `#` |
//! | Zero-padding | `0` |
//! | Width | `{:5}` |
//! | Precision | `{:.2}` |
//! | Type | `?` `x` `X` `o` `b` `e` `E` `p` |
//!
//! ## Performance Considerations
//!
//! The crate is designed with performance in mind. The `FormatString` can be created once and reused multiple times with different arguments.
//! This is particularly useful in scenarios where the same format string is used repeatedly.
//!
//! ```rust
//! use dyf::{dformat, FormatString};
//!
//! let fmt = FormatString::from_string("The value is: {:>10}".to_string()).unwrap();
//! let result1 = dformat!(&fmt, 42).unwrap();
//! let result2 = dformat!(&fmt, 100).unwrap();
//! assert_eq!(result1, format!("The value is: {:>10}", 42));
//! assert_eq!(result2, format!("The value is: {:>10}", 100));
//! ```
//!
//! ## Limitations
//!
//! While this crate aims to support all standard Rust format specifiers, there might be some edge cases that are not yet covered.
//! If you encounter any unsupported format specifiers or have suggestions for improvements, please open an issue on the GitHub repository.
//!
//! ## Contributing
//!
//! Contributions are welcome! Please open an issue or submit a pull request on the GitHub repository.
//!
//! ## License
//!
//! This project is licensed under the GNU General Public License v3.0 (GPL-3.0).
//! By using this software, you agree to the terms and conditions of this license.
//!
//! The full license text is available in the LICENSE file in the project root or at:
//! [https://www.gnu.org/licenses/gpl-3.0.html](https://www.gnu.org/licenses/gpl-3.0.html)

use std::{
    borrow::Cow,
    fmt::{Debug, Display},
};

use pest::{Parser, iterators::Pair};
use thiserror::Error;

mod imp;
mod parser;
use parser::{FmtParser, Rule};

/// Errors that can occur during dynamic formatting.
///
/// This enum represents all possible errors that can occur during the parsing and
/// application of format specifications.
#[derive(Debug, Error)]
pub enum Error {
    /// An unsupported format specification was encountered.
    ///
    /// This error occurs when a format specification contains options or combinations
    /// that are not supported by the formatting machinery.
    #[error("unsupported format spec {0}")]
    UnsupportedSpec(FormatSpec),

    /// The number of arguments doesn't match the number of format specifications.
    ///
    /// This error occurs when the number of arguments provided to a format string
    /// doesn't match the number of format specifications in the string.
    ///
    /// # Examples
    ///
    /// Providing too few arguments:
    ///
    /// ```rust
    /// use dyf::{FormatString, dformat, Error};
    ///
    /// let fmt = FormatString::from_string("{}, {}".to_string()).unwrap();
    /// let result = dformat!(&fmt, "only one argument");
    /// assert!(matches!(result, Err(Error::ArgumentCountMismatch(2, 1))));
    /// ```
    ///
    /// Providing too many arguments:
    ///
    /// ```rust
    /// use dyf::{FormatString, dformat, Error};
    ///
    /// let fmt = FormatString::from_string("{}".to_string()).unwrap();
    /// let result = dformat!(&fmt, "one", "extra");
    /// assert!(matches!(result, Err(Error::ArgumentCountMismatch(1, 2))));
    /// ```
    #[error(
        "number of arguments doesn't match number of format specifications expected={0} found={1}"
    )]
    ArgumentCountMismatch(usize, usize),

    /// An error occurred during format string parsing.
    ///
    /// This error wraps parsing errors from the underlying [`pest`] parser and provides
    /// information about syntax errors in format strings.
    #[error("format parsing error: {0}")]
    Parse(#[from] Box<pest::error::Error<Rule>>),
}

/// A trait for dynamic display formatting.
///
/// This trait provides a way to implement custom formatting for types that need to support
/// dynamic format specifications at runtime. It's similar to the standard [`std::fmt::Display`] trait
/// but with additional formatting control through [`FormatSpec`].
///
/// # Examples
///
/// Basic implementation for a custom type:
///
/// ```
/// use dyf::{DynDisplay, FormatSpec, Error};
///
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl DynDisplay for Point {
///     fn dyn_fmt(&self, spec: &FormatSpec) -> Result<String, Error> {
///         let s = format!("Point({}, {})", self.x, self.y);
///         Ok(spec.fill_and_align(s, dyf::Align::Left))
///     }
/// }
/// ```
///
/// Implementation with format-aware behavior:
///
/// ```
/// use dyf::{DynDisplay, FormatSpec, Error, FmtType};
///
/// struct Color {
///     r: u8,
///     g: u8,
///     b: u8,
/// }
///
/// impl DynDisplay for Color {
///     fn dyn_fmt(&self, spec: &FormatSpec) -> Result<String, Error> {
///         match spec.ty {
///             FmtType::LowerHex => Ok(format!(
///                 "#{:02x}{:02x}{:02x}",
///                 self.r, self.g, self.b
///             )),
///             FmtType::UpperHex => Ok(format!(
///                 "#{:02X}{:02X}{:02X}",
///                 self.r, self.g, self.b
///             )),
///             FmtType::Debug => Ok(format!(
///                 "Color {{ r: {}, g: {}, b: {} }}",
///                 self.r, self.g, self.b
///             )),
///             _ => Ok(format!(
///                 "RGB({}, {}, {})",
///                 self.r, self.g, self.b
///             )),
///         }.map(|s| spec.fill_and_align(s, dyf::Align::Left))
///     }
/// }
/// ```
pub trait DynDisplay {
    /// Formats the value using the given format specification.
    ///
    /// # Arguments
    ///
    /// * `spec` - The format specification containing alignment, width, precision,
    ///   and other formatting options
    ///
    /// # Returns
    ///
    /// A `Result` containing the formatted string or an error if formatting fails.
    ///
    /// # Errors
    ///
    /// This function may return an error if the format specification is not supported
    /// for this type or if formatting fails for other reasons.
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error>;
}

/// Specifies the type of formatting to apply to a value.
///
/// The [`FmtType`] enum represents the various format types that can be specified
/// in a format string after the colon. These determine how values are converted
/// to strings, including different representations for numbers, debugging output,
/// and other special formats.
///
/// # Format String Representation
///
/// In format strings, these types are represented as follows:
///
/// | FmtType | Format Specifier | Description |
/// |---------|------------------|-------------|
/// | Default | (none) | Default formatting for the type |
/// | Debug | `?` | Debug representation |
/// | DebugLowHex | `x?` | Debug representation with lowercase hexadecimal |
/// | DebugUpHex | `X?` | Debug representation with uppercase hexadecimal |
/// | LowerHex | `x` | Lowercase hexadecimal |
/// | UpperHex | `X` | Uppercase hexadecimal |
/// | Octal | `o` | Octal representation |
/// | Ptr | `p` | Pointer address |
/// | Bin | `b` | Binary representation |
/// | LowExp | `e` | Lowercase exponential notation |
/// | UpperExp | `E` | Uppercase exponential notation |
///
/// # Examples
///
/// Basic usage with format specifications:
///
/// ```
/// use dyf::{FmtType, FormatSpec};
///
/// // Create a format specification for hexadecimal output
/// let hex_spec = FormatSpec {
///     ty: FmtType::LowerHex,
///     ..Default::default()
/// };
///
/// // Create a format specification for debug output
/// let debug_spec = FormatSpec {
///     ty: FmtType::Debug,
///     ..Default::default()
/// };
/// ```
///
/// Using with custom formatting:
///
/// ```
/// use dyf::{FmtType, FormatSpec, DynDisplay, Error};
///
/// struct Color {
///     r: u8,
///     g: u8,
///     b: u8,
/// }
///
/// impl DynDisplay for Color {
///     fn dyn_fmt(&self, spec: &FormatSpec) -> Result<String, Error> {
///         match spec.ty {
///             FmtType::LowerHex => Ok(format!(
///                 "#{:02x}{:02x}{:02x}",
///                 self.r, self.g, self.b
///             )),
///             FmtType::UpperHex => Ok(format!(
///                 "#{:02X}{:02X}{:02X}",
///                 self.r, self.g, self.b
///             )),
///             FmtType::Debug => Ok(format!(
///                 "Color {{ r: {}, g: {}, b: {} }}",
///                 self.r, self.g, self.b
///             )),
///             _ => Ok(format!(
///                 "RGB({}, {}, {})",
///                 self.r, self.g, self.b
///             )),
///         }
///     }
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub enum FmtType {
    /// Default formatting for the type.
    ///
    /// This uses the standard display formatting for the type, equivalent to not
    /// specifying a format type in the format string.
    Default,

    /// Debug representation.
    ///
    /// This uses the debug formatting for the type, equivalent to the `{:?}` format specifier.
    Debug,

    /// Debug representation with lowercase hexadecimal.
    ///
    /// This combines debug formatting with lowercase hexadecimal representation.
    DebugLowHex,

    /// Debug representation with uppercase hexadecimal.
    ///
    /// This combines debug formatting with uppercase hexadecimal representation.
    DebugUpHex,

    /// Lowercase hexadecimal representation.
    ///
    /// This formats numbers in lowercase hexadecimal, equivalent to the `{:x}` format specifier.
    LowerHex,

    /// Uppercase hexadecimal representation.
    ///
    /// This formats numbers in uppercase hexadecimal, equivalent to the `{:X}` format specifier.
    UpperHex,

    /// Octal representation.
    ///
    /// This formats numbers in octal (base-8), equivalent to the `{:o}` format specifier.
    Octal,

    /// Pointer address representation.
    ///
    /// This formats pointer values as memory addresses, equivalent to the `{:p}` format specifier.
    Ptr,

    /// Binary representation.
    ///
    /// This formats numbers in binary (base-2), equivalent to the `{:b}` format specifier.
    Bin,

    /// Lowercase exponential notation.
    ///
    /// This formats floating-point numbers in scientific notation with lowercase 'e',
    /// equivalent to the `{:e}` format specifier.
    LowExp,

    /// Uppercase exponential notation.
    ///
    /// This formats floating-point numbers in scientific notation with uppercase 'E',
    /// equivalent to the `{:E}` format specifier.
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

/// Specifies the alignment of formatted text within a field width.
///
/// The [`Align`] enum determines how text should be aligned when a width is specified
/// in a format specification. It controls whether the text is left-aligned, right-aligned,
/// or centered within the allocated space.
#[derive(Debug, Clone, Copy)]
pub enum Align {
    /// Left-align the text within the field.
    ///
    /// When this alignment is used, text is placed at the beginning of the field,
    /// with any padding added to the right.
    Left,

    /// Center the text within the field.
    ///
    /// When this alignment is used, text is placed in the middle of the field,
    /// with padding distributed equally on both sides when possible.
    Center,

    /// Right-align the text within the field.
    ///
    /// When this alignment is used, text is placed at the end of the field,
    /// with any padding added to the left.
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

/// Specifies how signs should be displayed for numeric values.
///
/// The [`Sign`] enum controls the display of signs for numeric values in formatted output.
/// It determines whether positive numbers should show a plus sign, only negative numbers
/// should show a minus sign, or no special sign handling should be applied.
///
/// # Format Specification
///
/// In format strings, these correspond to:
/// - `+` for `Sign::Positive` (show signs for both positive and negative numbers)
/// - `-` for `Sign::Negative` (show signs only for negative numbers, default behavior)
#[derive(Debug, Clone, Copy)]
pub enum Sign {
    /// Always show the sign for numeric values.
    ///
    /// Positive numbers will be prefixed with `+`, and negative numbers with `-`.
    /// This corresponds to the `+` format specifier.
    Positive,

    /// Only show the sign for negative numbers.
    ///
    /// Negative numbers will be prefixed with `-`, while positive numbers will
    /// have no sign prefix. This is the default behavior and corresponds to
    /// the `-` format specifier.
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

/// A complete format specification for dynamic formatting.
///
/// [`FormatSpec`] represents all the components of a format specification that can appear
/// between the colons in a format string: `"{:<5.2}"`. It controls how values are formatted
/// including alignment, padding, width, precision, and type-specific formatting.
///
/// # Format String Components
///
/// A format specification in a string typically looks like:
/// `:[fill][align][sign][#][0][width][.precision][type]`
#[derive(Debug, Clone)]
pub struct FormatSpec {
    /// The fill character to use for padding.
    ///
    /// If `None`, spaces will be used for padding.
    pub fill: Option<char>,

    /// The alignment of the formatted value within the field.
    ///
    /// If `None`, the default alignment (typically right for numbers, left for text) will be used.
    pub align: Option<Align>,

    /// The sign display option for numeric values.
    ///
    /// If `None`, signs will only be shown for negative numbers.
    pub sign: Option<Sign>,

    /// Whether to use alternate formatting.
    ///
    /// For example, adding `0x` prefix to hexadecimal numbers or always showing the decimal point.
    pub alternate: bool,

    /// Whether to pad with zeros instead of the fill character.
    ///
    /// This is typically used for numeric types to ensure a minimum number of digits.
    pub zero: bool,

    /// The minimum width of the formatted field.
    ///
    /// If the formatted value is shorter than this width, it will be padded according to the alignment.
    pub width: Option<usize>,

    /// The precision for floating-point numbers or maximum length for strings.
    pub precision: Option<usize>,

    /// The format type specification.
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

    /// Applies fill and alignment to a string according to this format specification.
    ///
    /// # Arguments
    ///
    /// * `s` - The string to format
    /// * `default_align` - The default alignment to use if none is specified
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

/// A parsed format string that can be used for dynamic formatting.
///
/// [`FormatString`] represents a string with embedded format specifications that has been
/// parsed and can be used with the [`dformat!`] macro to perform dynamic formatting operations.
/// It contains the original string along with information about the format specifications
/// found within it.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use dyf::FormatString;
///
/// let fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
/// assert!(fmt.contains_format());
/// ```
///
/// Creating and using a format string:
///
/// ```
/// use dyf::{FormatString, dformat};
///
/// let fmt = FormatString::from_string("{:>10} {:.2}".to_string()).unwrap();
/// let result = dformat!(&fmt, 42, 3.14159).unwrap();
/// assert_eq!(result, "        42 3.14");
/// ```
///
/// Converting between string types:
///
/// ```
/// use dyf::FormatString;
///
/// let fmt = FormatString::from_string("Value: {:05}".to_string()).unwrap();
/// let fmt_str = fmt.to_string_lossy();
/// let owned_str = fmt.into_string();
/// ```
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

    /// Creates a new [`FormatString`] from a string.
    ///
    /// # Arguments
    ///
    /// * `s` - The string containing format specifications
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed [`FormatString`] or an error if parsing fails.
    ///
    /// # Errors
    ///
    /// This function may return an error if the input string contains invalid format
    /// specifications that cannot be parsed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::FormatString;
    ///
    /// let fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
    /// ```
    pub fn from_string(s: String) -> Result<Self, Error> {
        Self::new_from_str(s)
    }

    /// Converts the [`FormatString`] into its inner string.
    ///
    /// This consumes the [`FormatString`] and returns the original string that was used
    /// to create it.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::FormatString;
    ///
    /// let fmt = FormatString::from_string("Test: {}".to_string()).unwrap();
    /// let s = fmt.into_string();
    /// assert_eq!(s, "Test: {}");
    /// ```
    pub fn into_string(self) -> String {
        self.s
    }

    /// Returns a borrowed version of the format string.
    ///
    /// This provides access to the original string without consuming the [`FormatString`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::FormatString;
    ///
    /// let fmt = FormatString::from_string("Value: {:.2}".to_string()).unwrap();
    /// let borrowed = fmt.to_string_lossy();
    /// assert_eq!(&*borrowed, "Value: {:.2}");
    /// ```
    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        Cow::Borrowed(&self.s)
    }

    /// Returns `true` if the format string contains any format specifications.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::FormatString;
    ///
    /// let with_fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
    /// assert!(with_fmt.contains_format());
    ///
    /// let without_fmt = FormatString::from_string("Hello, world!".to_string()).unwrap();
    /// assert!(!without_fmt.contains_format());
    /// ```
    pub fn contains_format(&self) -> bool {
        !self.fmts.is_empty()
    }
}

/// A formatter that applies format specifications to values.
///
/// The `Formatter` struct collects arguments and applies format specifications to them
/// to build the final formatted string. It collects all arguments first using [`Formatter::push_arg`]
/// and then performs the formatting in one operation with the [`Formatter::format`] method.
///
/// # Examples
///
/// Basic usage with a format string:
///
/// ```
/// use dyf::{FormatString, Formatter};
///
/// let fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
/// let mut formatter = Formatter::from(&fmt);
/// formatter.push_arg(&"world").format().unwrap();
/// assert_eq!(formatter.into_string(), "Hello, world!");
/// ```
///
/// Formatting multiple values:
///
/// ```
/// use dyf::{FormatString, Formatter};
///
/// let fmt = FormatString::from_string("{}, {}!".to_string()).unwrap();
/// let mut formatter = Formatter::from(&fmt);
/// formatter.push_arg(&"Hello").push_arg(&"world").format().unwrap();
/// assert_eq!(formatter.into_string(), "Hello, world!");
/// ```
///
/// Using with custom types:
///
/// ```
/// use dyf::{FormatString, Formatter, DynDisplay, Error, FormatSpec};
///
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl DynDisplay for Point {
///     fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
///         let s = format!("Point({}, {})", self.x, self.y);
///         Ok(f.fill_and_align(s, dyf::Align::Left))
///     }
/// }
///
/// let fmt = FormatString::from_string("Point: {}".to_string()).unwrap();
/// let point = Point { x: 10, y: 20 };
/// let mut formatter = Formatter::from(&fmt);
/// formatter.push_arg(&point).format().unwrap();
/// assert_eq!(formatter.into_string(), "Point: Point(10, 20)");
/// ```
pub struct Formatter<'s> {
    /// index in the format string
    i: usize,
    format_string: &'s FormatString,
    args: Vec<&'s dyn DynDisplay>,
    out: String,
}

impl<'s> From<&'s FormatString> for Formatter<'s> {
    fn from(value: &'s FormatString) -> Self {
        Self {
            i: 0,
            format_string: value,
            args: vec![],
            out: String::new(),
        }
    }
}

impl<'s> Formatter<'s> {
    /// Adds an argument to be formatted.
    ///
    /// This method collects arguments that will be formatted when [`Formatter::format`] is called.
    /// It supports method chaining for convenient use.
    ///
    /// # Arguments
    ///
    /// * `arg` - The argument to format, which must implement [`DynDisplay`]
    ///
    /// # Returns
    ///
    /// A mutable reference to the formatter for method chaining.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::{FormatString, Formatter};
    ///
    /// let fmt = FormatString::from_string("{}, {}!".to_string()).unwrap();
    /// let mut formatter = Formatter::from(&fmt);
    /// formatter.push_arg(&"Hello").push_arg(&"world");
    /// ```
    pub fn push_arg<A>(&mut self, arg: &'s A) -> &mut Self
    where
        A: DynDisplay,
    {
        self.args.push(arg);
        self
    }

    /// Applies the format specifications to all collected arguments.
    ///
    /// This method performs the actual formatting after all arguments have been collected
    /// with [`Formatter::push_arg`]. It verifies that the number of arguments matches the number of
    /// format specifications in the format string.
    ///
    /// # Returns
    ///
    /// A mutable reference to the formatter for method chaining.
    ///
    /// # Errors
    ///
    /// Returns an error if the number of arguments doesn't match the number of format
    /// specifications, or if any individual formatting operation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::{FormatString, Formatter};
    ///
    /// let fmt = FormatString::from_string("{:>5}, {:<5}".to_string()).unwrap();
    /// let mut formatter = Formatter::from(&fmt);
    /// formatter.push_arg(&42).push_arg(&"hello").format().unwrap();
    /// assert_eq!(formatter.into_string(), "   42, hello");
    /// ```
    pub fn format(&mut self) -> Result<&mut Self, Error> {
        if self.args.len() != self.format_string.fmts.len() {
            return Err(Error::ArgumentCountMismatch(
                // expected
                self.format_string.fmts.len(),
                // found
                self.args.len(),
            ));
        }

        for (i, a) in self.args.iter().enumerate() {
            // this cannot panic as lengths are equal
            let arg_fmt = &self.format_string.fmts[i];
            let slice = &self.format_string.s.as_str()[self.i..];
            self.out.push_str(&slice[..arg_fmt.start - self.i]);
            self.out.push_str(&arg_fmt.dyn_fmt_arg(a)?);
            self.i = arg_fmt.end;
        }

        // we copy the rest of the string
        let slice = &self.format_string.s.as_str()[self.i..];
        self.out.push_str(slice);

        Ok(self)
    }

    /// Returns a borrowed version of the formatted string.
    ///
    /// This provides access to the current state of the formatted string without
    /// consuming the formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::{FormatString, Formatter};
    ///
    /// let fmt = FormatString::from_string("Value: {}".to_string()).unwrap();
    /// let mut formatter = Formatter::from(&fmt);
    /// formatter.push_arg(&42).format().unwrap();
    /// let borrowed = formatter.to_string_lossy();
    /// assert_eq!(&*borrowed, "Value: 42");
    /// ```
    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        Cow::Borrowed(&self.out)
    }

    /// Consumes the formatter and returns the formatted string.
    ///
    /// This finalizes the formatting process and returns the complete formatted string.
    ///
    /// # Examples
    ///
    /// ```
    /// use dyf::{FormatString, Formatter};
    ///
    /// let fmt = FormatString::from_string("The answer is: {}".to_string()).unwrap();
    /// let mut formatter = Formatter::from(&fmt);
    /// formatter.push_arg(&42).format().unwrap();
    /// let result = formatter.into_string();
    /// assert_eq!(result, "The answer is: 42");
    /// ```
    pub fn into_string(self) -> String {
        self.out
    }
}

/// Dynamically formats values according to a format string.
///
/// The `dformat!` macro provides functionality similar to Rust's standard `format!` macro,
/// but with dynamic formatting capabilities. It uses a pre-parsed [`FormatString`] to
/// apply format specifications to values at runtime.
///
/// # Syntax
///
/// The macro takes two arguments:
/// - A reference to a [`FormatString`] that has been created from a format string
/// - A list of arguments to format
///
/// ```ignore
/// dformat!(format_string_ref, arg1, arg2, ...)
/// ```
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use dyf::{FormatString, dformat};
///
/// let fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
/// let result = dformat!(&fmt, "world").unwrap();
/// assert_eq!(result, "Hello, world!");
/// ```
///
/// Formatting with different specifications:
///
/// ```
/// use dyf::{FormatString, dformat};
///
/// let fmt = FormatString::from_string("{:>5}, {:.2}".to_string()).unwrap();
/// let result = dformat!(&fmt, 42, 3.14159).unwrap();
/// assert_eq!(result, "   42, 3.14");
/// ```
///
/// Using with custom types that implement [`DynDisplay`]:
///
/// ```
/// use dyf::{FormatString, dformat, DynDisplay, Error, FormatSpec};
///
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl DynDisplay for Point {
///     fn dyn_fmt(&self, spec: &FormatSpec) -> Result<String, Error> {
///         let s = format!("Point({}, {})", self.x, self.y);
///         Ok(spec.fill_and_align(s, dyf::Align::Left))
///     }
/// }
///
/// let fmt = FormatString::from_string("Point: {}".to_string()).unwrap();
/// let point = Point { x: 10, y: 20 };
/// let result = dformat!(&fmt, point).unwrap();
/// assert_eq!(result, "Point: Point(10, 20)");
/// ```
///
/// # Errors
///
/// The macro returns a `Result<String, Error>`. Any error might be one
/// of the [`Error`] variant.
///
/// # Performance Considerations
///
/// For best performance when formatting the same string multiple times:
/// 1. Create the `FormatString` once and reuse it
/// 2. Use the `dformat!` macro for each formatting operation
///
/// ```
/// use dyf::{FormatString, dformat};
///
/// let fmt = FormatString::from_string("Value: {:>10}".to_string()).unwrap();
/// let result1 = dformat!(&fmt, 42).unwrap();
/// let result2 = dformat!(&fmt, "text").unwrap();
/// ```
///
/// # Comparison with Standard `format!` Macro
///
/// While similar to Rust's standard `format!` macro, `dformat!` provides:
/// - Dynamic formatting capabilities through the `DynDisplay` trait
/// - The ability to pre-parse format strings for reuse
///
/// However, for simple cases where you don't need these features, the standard `format!`
/// macro is recommended.
#[macro_export]
macro_rules! dformat {
    ($fmt: expr, $($arg: expr),*) => {
        {
            let mut fs = $crate::Formatter::from($fmt);
            $(
                fs.push_arg(&$arg);
            )*

            match fs.format() {
                Err(e) => Err(e),
                Ok(_) => Ok(fs.into_string()),
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
            format!("Hello, {}!", "world"),
            dformat_lit!("Hello, {}!", "world").unwrap()
        );
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
