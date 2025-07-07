use std::{
    borrow::Cow,
    ffi::{OsStr, OsString},
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
    time::{Duration, Instant, SystemTime},
};

use crate::{Align, DynDisplay, Error, FmtType, FormatSpec, Sign};

macro_rules! impl_debug {
    ($ty:ty) => {
        impl DynDisplay for $ty {
            fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
                match f.ty {
                    FmtType::Debug => {
                        if f.alternate {
                            Ok(format!("{:#?}", self))
                        } else {
                            Ok(format!("{:?}", self))
                        }
                    }
                    FmtType::Default
                    | FmtType::DebugLowHex
                    | FmtType::DebugUpHex
                    | FmtType::LowerHex
                    | FmtType::UpperHex
                    | FmtType::Octal
                    | FmtType::Ptr
                    | FmtType::Bin
                    | FmtType::LowExp
                    | FmtType::UpperExp => Err(Error::UnsupportedSpec(f.clone())),
                }
                .map(|s| f.fill_and_align(s, Align::Left))
            }
        }
    };
}

macro_rules! impl_debug_display {
    ($ty:ty) => {
        impl DynDisplay for $ty {
            fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
                match f.ty {
                    FmtType::Debug => {
                        if f.alternate {
                            Ok(format!("{:#?}", self))
                        } else {
                            Ok(format!("{:?}", self))
                        }
                    }
                    FmtType::Default => Ok(format!("{}", self)),
                    FmtType::DebugLowHex
                    | FmtType::DebugUpHex
                    | FmtType::LowerHex
                    | FmtType::UpperHex
                    | FmtType::Octal
                    | FmtType::Ptr
                    | FmtType::Bin
                    | FmtType::LowExp
                    | FmtType::UpperExp => Err(Error::UnsupportedSpec(f.clone())),
                }
                .map(|s| f.fill_and_align(s, Align::Left))
            }
        }
    };
}

impl DynDisplay for char {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        match f.ty {
            FmtType::Debug => {
                if f.alternate {
                    Ok(format!("{:#?}", self))
                } else {
                    Ok(format!("{:?}", self))
                }
            }
            FmtType::Default => Ok(format!("{}", self)),
            FmtType::DebugLowHex
            | FmtType::DebugUpHex
            | FmtType::LowerHex
            | FmtType::UpperHex
            | FmtType::Octal
            | FmtType::Ptr
            | FmtType::Bin
            | FmtType::LowExp
            | FmtType::UpperExp => Err(Error::UnsupportedSpec(f.clone())),
        }
        .map(|s| f.fill_and_align(s, Align::Left))
    }
}

impl_debug_display!(bool);

impl<T> DynDisplay for *const T {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        let ptr = *self;
        match f.ty {
            FmtType::Debug => {
                if f.alternate {
                    Ok(format!("{:#?}", ptr))
                } else {
                    Ok(format!("{:?}", ptr))
                }
            }
            FmtType::Ptr => Ok(format!("{:p}", ptr)),
            FmtType::Default
            | FmtType::DebugLowHex
            | FmtType::DebugUpHex
            | FmtType::LowerHex
            | FmtType::UpperHex
            | FmtType::Octal
            | FmtType::Bin
            | FmtType::LowExp
            | FmtType::UpperExp => Err(Error::UnsupportedSpec(f.clone())),
        }
        .map(|s| f.fill_and_align(s, Align::Right))
    }
}

impl<T> DynDisplay for *mut T {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        let ptr = *self;
        match f.ty {
            FmtType::Debug => {
                if f.alternate {
                    Ok(format!("{:#?}", ptr))
                } else {
                    Ok(format!("{:?}", ptr))
                }
            }
            FmtType::Ptr => Ok(format!("{:p}", ptr)),
            FmtType::Default
            | FmtType::DebugLowHex
            | FmtType::DebugUpHex
            | FmtType::LowerHex
            | FmtType::UpperHex
            | FmtType::Octal
            | FmtType::Bin
            | FmtType::LowExp
            | FmtType::UpperExp => Err(Error::UnsupportedSpec(f.clone())),
        }
        .map(|s| f.fill_and_align(s, Align::Right))
    }
}

impl DynDisplay for &str {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        match f.ty {
            FmtType::Debug => {
                if f.alternate {
                    Ok(format!("{:#?}", self))
                } else {
                    Ok(format!("{:?}", self))
                }
            }
            FmtType::DebugLowHex => Ok(format!("{:x?}", self)),
            FmtType::DebugUpHex => Ok(format!("{:X?}", self)),
            FmtType::Default => match (f.width, f.precision) {
                (None, None) => Ok(self.to_string()),
                (Some(w), None) => match f.align {
                    Some(Align::Left) => Ok(format!("{:<1$}", self, w)),
                    Some(Align::Center) => Ok(format!("{:^1$}", self, w)),
                    Some(Align::Right) => Ok(format!("{:>1$}", self, w)),
                    None => Ok(format!("{:1$}", self, w)),
                },
                (None, Some(p)) => Ok(format!("{:.1$}", self, p)),
                (Some(w), Some(p)) => match f.align {
                    Some(Align::Left) => Ok(format!("{:<1$.2$}", self, w, p)),
                    Some(Align::Center) => Ok(format!("{:^1$.2$}", self, w, p)),
                    Some(Align::Right) => Ok(format!("{:>1$.2$}", self, w, p)),
                    None => Ok(format!("{:1$.2$}", self, w, p)),
                },
            },
            FmtType::Ptr => {
                if f.alternate {
                    Ok(format!("{:#p}", self))
                } else {
                    Ok(format!("{:p}", self))
                }
            }
            FmtType::LowerHex
            | FmtType::UpperHex
            | FmtType::Bin
            | FmtType::Octal
            | FmtType::LowExp
            | FmtType::UpperExp => Err(Error::UnsupportedSpec(f.clone())),
        }
    }
}

impl DynDisplay for str {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        DynDisplay::dyn_fmt(&self, f)
    }
}

impl DynDisplay for String {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        if matches!(f.ty, FmtType::Ptr) {
            return Err(Error::UnsupportedSpec(f.clone()));
        }
        DynDisplay::dyn_fmt(&self.as_str(), f)
    }
}

macro_rules! impl_dyn_display_float {
    ($ty: ty) => {
        impl DynDisplay for $ty {
            #[inline]
            fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
                match f.ty {
                    FmtType::Debug => {
                        if f.alternate {
                            Ok(format!("{:#?}", self))
                        } else {
                            Ok(format!("{:?}", self))
                        }
                    }
                    FmtType::DebugUpHex => Ok(format!("{:X?}", self)),
                    FmtType::DebugLowHex => Ok(format!("{:x?}", self)),
                    FmtType::Default => match (f.precision, f.sign) {
                        (None, None) => Ok(format!("{}", self)),
                        (Some(p), None) => Ok(format!("{:.1$}", self, p)),
                        (None, Some(s)) => match s {
                            Sign::Positive => Ok(format!("{:+}", self)),
                            Sign::Negative => Ok(format!("{:-}", self)),
                        },
                        (Some(p), Some(s)) => match s {
                            Sign::Positive => Ok(format!("{:+.1$}", self, p)),
                            Sign::Negative => Ok(format!("{:-.1$}", self, p)),
                        },
                    },
                    FmtType::LowExp => match (f.precision, f.sign) {
                        (None, None) => Ok(format!("{:e}", self)),
                        (Some(p), None) => Ok(format!("{:.1$e}", self, p)),
                        (None, Some(s)) => match s {
                            Sign::Positive => Ok(format!("{:+e}", self)),
                            Sign::Negative => Ok(format!("{:-e}", self)),
                        },
                        (Some(p), Some(s)) => match s {
                            Sign::Positive => Ok(format!("{:+.1$e}", self, p)),
                            Sign::Negative => Ok(format!("{:-.1$e}", self, p)),
                        },
                    },
                    FmtType::UpperExp => match (f.precision, f.sign) {
                        (None, None) => Ok(format!("{:E}", self)),
                        (Some(p), None) => Ok(format!("{:.1$E}", self, p)),
                        (None, Some(s)) => match s {
                            Sign::Positive => Ok(format!("{:+E}", self)),
                            Sign::Negative => Ok(format!("{:-E}", self)),
                        },
                        (Some(p), Some(s)) => match s {
                            Sign::Positive => Ok(format!("{:+.1$E}", self, p)),
                            Sign::Negative => Ok(format!("{:-.1$E}", self, p)),
                        },
                    },
                    FmtType::Ptr
                    | FmtType::Bin
                    | FmtType::LowerHex
                    | FmtType::Octal
                    | FmtType::UpperHex => Err(Error::UnsupportedSpec(f.clone())),
                }
                .map(|s| f.fill_and_align(s, Align::Right))
            }
        }
    };
}

impl_dyn_display_float!(f32);
impl_dyn_display_float!(f64);

macro_rules! impl_dyn_display_int {
    ($ty: ty) => {
        impl DynDisplay for $ty {
            fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
                match f.ty {
                    FmtType::Default => match (f.alternate, f.zero) {
                        (true, true) => {
                            if let Some(w) = f.width {
                                Ok(format!("{:#01$}", self, w))
                            } else {
                                Ok(format!("{:#0}", self))
                            }
                        }
                        (true, false) => Ok(format!("{:#}", self)),
                        (false, true) => {
                            if let Some(w) = f.width {
                                Ok(format!("{:01$}", self, w))
                            } else {
                                Ok(format!("{:0}", self))
                            }
                        }
                        (false, false) => {
                            // sign is used only if not alternate / zero
                            if let Some(s) = f.sign {
                                match s {
                                    Sign::Positive => Ok(format!("{:+}", self)),
                                    Sign::Negative => Ok(format!("{:-}", self)),
                                }
                            } else {
                                Ok(format!("{:}", self))
                            }
                        }
                    },
                    FmtType::Debug => {
                        if f.alternate {
                            Ok(format!("{:#?}", self))
                        } else {
                            Ok(format!("{:?}", self))
                        }
                    }
                    FmtType::LowerHex => match (f.alternate, f.zero) {
                        (true, true) => Ok(format!("{:#0x}", self)),
                        (true, false) => Ok(format!("{:#x}", self)),
                        (false, true) => Ok(format!("{:0x}", self)),
                        (false, false) => Ok(format!("{:x}", self)),
                    },
                    FmtType::UpperHex => match (f.alternate, f.zero) {
                        (true, true) => Ok(format!("{:#0X}", self)),
                        (true, false) => Ok(format!("{:#X}", self)),
                        (false, true) => Ok(format!("{:0X}", self)),
                        (false, false) => Ok(format!("{:X}", self)),
                    },
                    FmtType::Bin => match (f.alternate, f.zero) {
                        (true, true) => Ok(format!("{:#0b}", self)),
                        (true, false) => Ok(format!("{:#b}", self)),
                        (false, true) => Ok(format!("{:0b}", self)),
                        (false, false) => Ok(format!("{:b}", self)),
                    },
                    FmtType::Octal => match (f.alternate, f.zero) {
                        (true, true) => Ok(format!("{:#0o}", self)),
                        (true, false) => Ok(format!("{:#o}", self)),
                        (false, true) => Ok(format!("{:0o}", self)),
                        (false, false) => Ok(format!("{:o}", self)),
                    },
                    // LowExp doesn't use zero / alternate
                    FmtType::LowExp => Ok(format!("{:e}", self)),
                    // UpperExp doesn't use zero / alternate
                    FmtType::UpperExp => Ok(format!("{:E}", self)),
                    FmtType::Ptr => {
                        if f.alternate {
                            Ok(format!("{:#p}", self))
                        } else {
                            Ok(format!("{:p}", self))
                        }
                    }

                    // Special handling for debug-with-hex
                    FmtType::DebugLowHex => {
                        if f.alternate {
                            Ok(format!("{:#x?}", self))
                        } else {
                            Ok(format!("{:x?}", self))
                        }
                    }
                    FmtType::DebugUpHex => {
                        if f.alternate {
                            Ok(format!("{:#X?}", self))
                        } else {
                            Ok(format!("{:X?}", self))
                        }
                    }
                }
                .map(|s| f.fill_and_align(s, Align::Right))
            }
        }
    };
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

impl<T: DynDisplay> DynDisplay for Box<T> {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl<T: DynDisplay> DynDisplay for Rc<T> {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl<T: DynDisplay> DynDisplay for Arc<T> {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl<T: DynDisplay + Clone> DynDisplay for Cow<'_, T> {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl DynDisplay for Cow<'_, str> {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

// network
impl_debug_display!(IpAddr);
impl_debug_display!(Ipv4Addr);
impl_debug_display!(Ipv6Addr);
impl_debug_display!(SocketAddr);
impl_debug_display!(SocketAddrV4);
impl_debug_display!(SocketAddrV6);

// time
impl_debug!(Duration);
impl_debug!(SystemTime);
impl_debug!(Instant);

// path
impl_debug!(&Path);
impl_debug!(PathBuf);

// ffi
impl_debug!(OsString);
impl_debug!(&OsStr);

impl DynDisplay for &dyn DynDisplay {
    fn dyn_fmt(&self, f: &FormatSpec) -> Result<String, Error> {
        (*self).dyn_fmt(f)
    }
}
