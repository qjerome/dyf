use std::{
    borrow::Cow,
    ffi::{OsStr, OsString},
    fmt::Write,
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
    time::{Duration, Instant, SystemTime},
};

use crate::{Align, DynDisplay, Error, FmtType, Formatter, Sign};

macro_rules! impl_debug {
    ($ty:ty) => {
        impl DynDisplay for $ty {
            fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
                f.set_default_align(Align::Left);
                match f.fmt_type() {
                    FmtType::Debug => {
                        if f.alternate() {
                            Ok(write!(f, "{self:#?}")?)
                        } else {
                            Ok(write!(f, "{self:?}")?)
                        }
                    }
                    _ => Err(Error::UnsupportedSpec(f.spec().clone())),
                }
            }
        }
    };
}

macro_rules! impl_debug_display {
    ($ty:ty) => {
        impl DynDisplay for $ty {
            fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
                f.set_default_align(Align::Left);
                match f.fmt_type() {
                    FmtType::Debug => {
                        if f.alternate() {
                            Ok(write!(f, "{self:#?}")?)
                        } else {
                            Ok(write!(f, "{self:?}")?)
                        }
                    }
                    FmtType::Default => Ok(write!(f, "{self}")?),
                    _ => Err(Error::UnsupportedSpec(f.spec().clone())),
                }
            }
        }
    };
}

impl DynDisplay for char {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        f.set_default_align(Align::Left);
        match f.fmt_type() {
            FmtType::Debug => {
                if f.alternate() {
                    Ok(write!(f, "{self:#?}")?)
                } else {
                    Ok(write!(f, "{self:?}")?)
                }
            }
            FmtType::Default => Ok(write!(f, "{self}")?),
            _ => Err(Error::UnsupportedSpec(f.spec().clone())),
        }
    }
}

impl_debug_display!(bool);

impl<T> DynDisplay for *const T {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        let ptr = *self;
        f.set_default_align(Align::Right);
        match f.fmt_type() {
            FmtType::Debug => {
                if f.alternate() {
                    Ok(write!(f, "{ptr:#?}")?)
                } else {
                    Ok(write!(f, "{ptr:?}")?)
                }
            }
            FmtType::Ptr => Ok(write!(f, "{ptr:p}")?),
            _ => Err(Error::UnsupportedSpec(f.spec().clone())),
        }
    }
}

impl<T> DynDisplay for *mut T {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        let ptr = *self;
        f.set_default_align(Align::Right);
        match f.fmt_type() {
            FmtType::Debug => {
                if f.alternate() {
                    Ok(write!(f, "{ptr:#?}")?)
                } else {
                    Ok(write!(f, "{ptr:?}")?)
                }
            }
            FmtType::Ptr => Ok(write!(f, "{ptr:p}")?),
            _ => Err(Error::UnsupportedSpec(f.spec().clone())),
        }
    }
}

impl DynDisplay for &str {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        f.set_default_align(Align::Left);
        match f.fmt_type() {
            FmtType::Debug => {
                if f.alternate() {
                    Ok(write!(f, "{self:#?}")?)
                } else {
                    Ok(write!(f, "{self:?}")?)
                }
            }
            FmtType::DebugLowHex => Ok(write!(f, "{self:x?}")?),
            FmtType::DebugUpHex => Ok(write!(f, "{self:X?}")?),
            FmtType::Default => {
                if let Some(p) = f.precision() {
                    Ok(write!(f, "{self:.p$}")?)
                } else {
                    Ok(write!(f, "{}", self)?)
                }
            }
            FmtType::Ptr => {
                if f.alternate() {
                    Ok(write!(f, "{self:#p}")?)
                } else {
                    Ok(write!(f, "{self:p}")?)
                }
            }
            _ => Err(Error::UnsupportedSpec(f.spec().clone())),
        }
    }
}

impl DynDisplay for str {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        DynDisplay::dyn_fmt(&self, f)
    }
}

impl DynDisplay for String {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        if matches!(f.fmt_type(), FmtType::Ptr) {
            return Err(Error::UnsupportedSpec(f.spec().clone()));
        }
        DynDisplay::dyn_fmt(&self.as_str(), f)
    }
}

macro_rules! impl_dyn_display_float {
    ($ty: ty) => {
        impl DynDisplay for $ty {
            #[inline]
            fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
                f.set_default_align(Align::Right);
                match f.fmt_type() {
                    FmtType::Debug => {
                        if f.alternate() {
                            Ok(write!(f, "{:#?}", self)?)
                        } else {
                            Ok(write!(f, "{:?}", self)?)
                        }
                    }
                    FmtType::DebugUpHex => Ok(write!(f, "{:X?}", self)?),
                    FmtType::DebugLowHex => Ok(write!(f, "{:x?}", self)?),
                    FmtType::Default => match (f.precision(), f.sign()) {
                        (None, None) => Ok(write!(f, "{}", self)?),
                        (Some(p), None) => Ok(write!(f, "{:.1$}", self, p)?),
                        (None, Some(s)) => match s {
                            Sign::Positive => Ok(write!(f, "{:+}", self)?),
                            Sign::Negative => Ok(write!(f, "{:-}", self)?),
                        },
                        (Some(p), Some(s)) => match s {
                            Sign::Positive => Ok(write!(f, "{:+.1$}", self, p)?),
                            Sign::Negative => Ok(write!(f, "{:-.1$}", self, p)?),
                        },
                    },
                    FmtType::LowExp => match (f.precision(), f.sign()) {
                        (None, None) => Ok(write!(f, "{:e}", self)?),
                        (Some(p), None) => Ok(write!(f, "{:.1$e}", self, p)?),
                        (None, Some(s)) => match s {
                            Sign::Positive => Ok(write!(f, "{:+e}", self)?),
                            Sign::Negative => Ok(write!(f, "{:-e}", self)?),
                        },
                        (Some(p), Some(s)) => match s {
                            Sign::Positive => Ok(write!(f, "{:+.1$e}", self, p)?),
                            Sign::Negative => Ok(write!(f, "{:-.1$e}", self, p)?),
                        },
                    },
                    FmtType::UpperExp => match (f.precision(), f.sign()) {
                        (None, None) => Ok(write!(f, "{:E}", self)?),
                        (Some(p), None) => Ok(write!(f, "{:.1$E}", self, p)?),
                        (None, Some(s)) => match s {
                            Sign::Positive => Ok(write!(f, "{:+E}", self)?),
                            Sign::Negative => Ok(write!(f, "{:-E}", self)?),
                        },
                        (Some(p), Some(s)) => match s {
                            Sign::Positive => Ok(write!(f, "{:+.1$E}", self, p)?),
                            Sign::Negative => Ok(write!(f, "{:-.1$E}", self, p)?),
                        },
                    },
                    _ => Err(Error::UnsupportedSpec(f.spec().clone())),
                }
            }
        }
    };
}

impl_dyn_display_float!(f32);
impl_dyn_display_float!(f64);

macro_rules! impl_dyn_display_int {
    ($ty: ty) => {
        impl DynDisplay for $ty {
            fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
                f.set_default_align(Align::Right);
                match f.fmt_type() {
                    FmtType::Default => match (f.alternate(), f.zero()) {
                        (true, true) => {
                            if let Some(w) = f.width() {
                                write!(f, "{:#01$}", self, w)
                            } else {
                                write!(f, "{:#0}", self)
                            }
                        }
                        (true, false) => write!(f, "{:#}", self),
                        (false, true) => {
                            if let Some(w) = f.width() {
                                write!(f, "{:01$}", self, w)
                            } else {
                                write!(f, "{:0}", self)
                            }
                        }
                        (false, false) => {
                            if let Some(s) = f.sign() {
                                match s {
                                    Sign::Positive => write!(f, "{:+}", self),
                                    Sign::Negative => write!(f, "{:-}", self),
                                }
                            } else {
                                write!(f, "{:}", self)
                            }
                        }
                    },
                    FmtType::Debug => {
                        if f.alternate() {
                            write!(f, "{:#?}", self)
                        } else {
                            write!(f, "{:?}", self)
                        }
                    }
                    FmtType::LowerHex => match (f.alternate(), f.zero()) {
                        (true, true) => write!(f, "{:#0x}", self),
                        (true, false) => write!(f, "{:#x}", self),
                        (false, true) => write!(f, "{:0x}", self),
                        (false, false) => write!(f, "{:x}", self),
                    },
                    FmtType::UpperHex => match (f.alternate(), f.zero()) {
                        (true, true) => write!(f, "{:#0X}", self),
                        (true, false) => write!(f, "{:#X}", self),
                        (false, true) => write!(f, "{:0X}", self),
                        (false, false) => write!(f, "{:X}", self),
                    },
                    FmtType::Bin => match (f.alternate(), f.zero()) {
                        (true, true) => write!(f, "{:#0b}", self),
                        (true, false) => write!(f, "{:#b}", self),
                        (false, true) => write!(f, "{:0b}", self),
                        (false, false) => write!(f, "{:b}", self),
                    },
                    FmtType::Octal => match (f.alternate(), f.zero()) {
                        (true, true) => write!(f, "{:#0o}", self),
                        (true, false) => write!(f, "{:#o}", self),
                        (false, true) => write!(f, "{:0o}", self),
                        (false, false) => write!(f, "{:o}", self),
                    },
                    FmtType::LowExp => write!(f, "{:e}", self),
                    FmtType::UpperExp => write!(f, "{:E}", self),
                    FmtType::Ptr => {
                        if f.alternate() {
                            write!(f, "{:#p}", self)
                        } else {
                            write!(f, "{:p}", self)
                        }
                    }
                    FmtType::DebugLowHex => {
                        if f.alternate() {
                            write!(f, "{:#x?}", self)
                        } else {
                            write!(f, "{:x?}", self)
                        }
                    }
                    FmtType::DebugUpHex => {
                        if f.alternate() {
                            write!(f, "{:#X?}", self)
                        } else {
                            write!(f, "{:X?}", self)
                        }
                    }
                }
                .map_err(|e| e.into())
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
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl<T: DynDisplay> DynDisplay for Rc<T> {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl<T: DynDisplay> DynDisplay for Arc<T> {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl<T: DynDisplay + Clone> DynDisplay for Cow<'_, T> {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        DynDisplay::dyn_fmt(self.as_ref(), f)
    }
}

impl DynDisplay for Cow<'_, str> {
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
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
    fn dyn_fmt(&self, f: &mut Formatter<'_>) -> crate::Result {
        (*self).dyn_fmt(f)
    }
}
