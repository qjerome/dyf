[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/qjerome/dyf/rust.yml?style=for-the-badge)](https://github.com/qjerome/dyf/actions/workflows/rust.yml)
[![Crates.io Version](https://img.shields.io/crates/v/dyf?style=for-the-badge)](https://crates.io/crates/dyf)
[![docs.rs](https://img.shields.io/docsrs/dyf?style=for-the-badge&logo=docs.rs&color=blue)](https://docs.rs/dyf)

<!-- cargo-rdme start -->

# Dynamic String Formatting for Rust (dyf)

The `dyf` crate brings dynamic string formatting to Rust while supporting the whole variety of string formats available in Rust.
It provides an easy way to implement dynamic formatting for custom types with the implementation of the `DynDisplay` trait.

## Features

- Support for all standard Rust format specifiers
- Dynamic formatting for custom types via the `DynDisplay` trait
- Macro support for convenient usage
- Support for various standard library types

## Usage

Add the crate to your project:

```sh
cargo add dyf
```

## Examples

### Basic Formatting

```rust
use dyf::{dformat, FormatString};

let fmt = FormatString::from_string("Hello, {}!".to_string()).unwrap();
let result = dformat!(&fmt, "world").unwrap();
assert_eq!(result, format!("Hello, {}!", "world"));

let num_fmt = FormatString::from_string("The answer is: {:>5}".to_string()).unwrap();
let num = 42;
let result = dformat!(&num_fmt, num).unwrap();
assert_eq!(result, format!("The answer is: {:>5}", num));
```

### Advanced Formatting

```rust
use dyf::{dformat, FormatString};

let fmt = FormatString::from_string("{:05} {:<10.2} {:^10}".to_string()).unwrap();
let result = dformat!(&fmt, 42, 42.1234, "hello").unwrap();
assert_eq!(result, format!("{:05} {:<10.2} {:^10}", 42, 42.1234, "hello"));
```

### Custom Type Formatting

```rust
use dyf::{DynDisplay, Error, FormatSpec, dformat, FormatString};

struct Point {
    x: i32,
    y: i32,
}

impl DynDisplay for Point {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        Ok(format!("Point({}, {})", self.x, self.y))
    }
}

impl std::fmt::Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Point({}, {})", self.x, self.y)
    }
}

let point = Point { x: 10, y: 20 };
let fmt = FormatString::from_string("{}".to_string()).unwrap();
let result = dformat!(&fmt, point).unwrap();
assert_eq!(result, format!("{}", point));
```

### Integer Formatting

```rust
use dyf::{dformat, FormatString};

// Decimal formatting
let fmt = FormatString::from_string("{}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{}", 42));

let fmt = FormatString::from_string("{:5}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:5}", 42));

let fmt = FormatString::from_string("{:05}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:05}", 42));

let fmt = FormatString::from_string("{:+}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:+}", 42));

// Hexadecimal formatting
let fmt = FormatString::from_string("{:x}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:x}", 42));

let fmt = FormatString::from_string("{:X}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:X}", 42));

// Octal formatting
let fmt = FormatString::from_string("{:o}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:o}", 42));

// Binary formatting
let fmt = FormatString::from_string("{:b}".to_string()).unwrap();
let result = dformat!(&fmt, 42).unwrap();
assert_eq!(result, format!("{:b}", 42));
```

### Float Formatting

```rust
use dyf::{dformat, FormatString};

let fmt = FormatString::from_string("{}".to_string()).unwrap();
let result = dformat!(&fmt, 42.0).unwrap();
assert_eq!(result, format!("{}", 42.0));

let fmt = FormatString::from_string("{:e}".to_string()).unwrap();
let result = dformat!(&fmt, 42.0).unwrap();
assert_eq!(result, format!("{:e}", 42.0));

let fmt = FormatString::from_string("{:.2}".to_string()).unwrap();
let result = dformat!(&fmt, 42.1234).unwrap();
assert_eq!(result, format!("{:.2}", 42.1234));

let fmt = FormatString::from_string("{:10.2}".to_string()).unwrap();
let result = dformat!(&fmt, 42.1234).unwrap();
assert_eq!(result, format!("{:10.2}", 42.1234));
```

### String Formatting

```rust
use dyf::{dformat, FormatString};

let fmt = FormatString::from_string("{}".to_string()).unwrap();
let result = dformat!(&fmt, "hello").unwrap();
assert_eq!(result, format!("{}", "hello"));

let fmt = FormatString::from_string("{:10}".to_string()).unwrap();
let result = dformat!(&fmt, "hello").unwrap();
assert_eq!(result, format!("{:10}", "hello"));

let fmt = FormatString::from_string("{:.3}".to_string()).unwrap();
let result = dformat!(&fmt, "hello").unwrap();
assert_eq!(result, format!("{:.3}", "hello"));
```

## Supported Format Specifiers

The crate supports all standard Rust format specifiers, including:

| Category | Specifiers |
|----------|------------|
| Fill/Alignment | `<` `>` `^` |
| Sign | `+` `-` |
| Alternate | `#` |
| Zero-padding | `0` |
| Width | `{:5}` `{:width$}` |
| Precision | `{:.2}` `{:.precision$}` |
| Type | `?` `x` `X` `o` `b` `e` `E` `p` |

## Performance Considerations

The crate is designed with performance in mind. The `FormatString` can be created once and reused multiple times with different arguments.
This is particularly useful in scenarios where the same format string is used repeatedly.

```rust
use dyf::{dformat, FormatString};

let fmt = FormatString::from_string("The value is: {:>10}".to_string()).unwrap();
let result1 = dformat!(&fmt, 42).unwrap();
let result2 = dformat!(&fmt, 100).unwrap();
assert_eq!(result1, format!("The value is: {:>10}", 42));
assert_eq!(result2, format!("The value is: {:>10}", 100));
```

## Limitations

While this crate aims to support all standard Rust format specifiers, there might be some edge cases that are not yet covered.
If you encounter any unsupported format specifiers or have suggestions for improvements, please open an issue on the GitHub repository.

## Contributing

Contributions are welcome! Please open an issue or submit a pull request on the GitHub repository.

## License

This project is licensed under the GNU General Public License v3.0 (GPL-3.0).
By using this software, you agree to the terms and conditions of this license.

The full license text is available in the LICENSE file in the project root or at:
[https://www.gnu.org/licenses/gpl-3.0.html](https://www.gnu.org/licenses/gpl-3.0.html)

<!-- cargo-rdme end -->
