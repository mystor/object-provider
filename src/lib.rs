#![cfg_attr(not(test), no_std)]
//! Trait for requesting values by type from a given object.
//!
//! # Examples
//!
//! ## Using a Provider
//!
//! ```
//! # use object_provider::*;
//! # use std::path::{Path, PathBuf};
//! # use std::fmt::Debug;
//! # struct MyProvider {
//! #     path: PathBuf,
//! # }
//! # impl ObjectProvider for MyProvider {
//! #     fn provide<'r, 'a>(&'a self, request: Request<'r, 'a>) -> ProvideResult<'r, 'a> {
//! #         request
//! #             .provide::<PathBuf>(&self.path)?
//! #             .provide::<Path>(&self.path)?
//! #             .provide::<dyn Debug>(&self.path)
//! #     }
//! # }
//! # let my_path = Path::new("hello/world");
//! # let my_provider = MyProvider { path: my_path.to_owned() };
//! let provider: &dyn ObjectProvider;
//! # provider = &my_provider;
//!
//! // It's possible to request concrete types like `PathBuf`
//! let path_buf = provider.request::<PathBuf>().unwrap();
//! assert_eq!(path_buf, my_path);
//!
//! // Requesting `!Sized` types, like slices and trait objects, is also supported.
//! let path = provider.request::<Path>().unwrap();
//! assert_eq!(path, my_path);
//!
//! let debug = provider.request::<dyn Debug>().unwrap();
//! assert_eq!(
//!     format!("{:?}", debug),
//!     format!("{:?}", my_path),
//! );
//!
//! // Types or interfaces not explicitly provided return `None`.
//! assert!(provider.request::<i32>().is_none());
//! assert!(provider.request::<dyn AsRef<Path>>().is_none());
//! ```
//!
//! ## Implementing a Provider
//!
//! ```
//! # use object_provider::*;
//! # use std::path::{Path, PathBuf};
//! # use std::fmt::Debug;
//! struct MyProvider {
//!     path: PathBuf,
//! }
//!
//! impl ObjectProvider for MyProvider {
//!     fn provide<'r, 'a>(&'a self, request: Request<'r, 'a>) -> ProvideResult<'r, 'a> {
//!         request
//!             .provide::<PathBuf>(&self.path)?
//!             .provide::<Path>(&self.path)?
//!             .provide::<dyn Debug>(&self.path)
//!     }
//! }
//! ```

use core::any::TypeId;
use core::cell::Cell;
use core::fmt;
use core::marker::PhantomData;
use core::ptr::NonNull;

/// A dynamic request for an object based on its type.
///
/// `'r` is the lifetime of request, and `'out` is the lifetime of the requested
/// reference.
pub struct Request<'r, 'out> {
    buf: NonNull<TypeId>,
    _marker: PhantomData<&'r mut &'out Cell<()>>,
}

impl<'r, 'out> Request<'r, 'out> {
    /// Provides an object of type `T` in response to this request.
    ///
    /// Returns `Err(FulfilledRequest)` if the value was successfully provided,
    /// and `Ok(self)` if `T` was not the type being requested.
    ///
    /// This method can be chained within `provide` implementations using the
    /// `?` operator to concisely provide multiple objects.
    pub fn provide<T: ?Sized + 'static>(self, value: &'out T) -> ProvideResult<'r, 'out> {
        self.provide_with(|| value)
    }

    /// Lazily provides an object of type `T` in response to this request.
    ///
    /// Returns `Err(FulfilledRequest)` if the value was successfully provided,
    /// and `Ok(self)` if `T` was not the type being requested.
    ///
    /// The passed closure is only called if the value will be successfully
    /// provided.
    ///
    /// This method can be chained within `provide` implementations using the
    /// `?` operator to concisely provide multiple objects.
    pub fn provide_with<T: ?Sized + 'static, F>(mut self, cb: F) -> ProvideResult<'r, 'out>
    where
        F: FnOnce() -> &'out T,
    {
        match self.downcast_buf::<T>() {
            Some(this) => {
                debug_assert!(this.value.is_none(), "Multiple requests to a `RequestBuf` were acquired?");
                this.value = Some(cb());
                Err(FulfilledRequest(PhantomData))
            }
            None => Ok(self),
        }
    }

    /// Get the `TypeId` of the requested type.
    pub fn type_id(&self) -> TypeId {
        unsafe { *self.buf.as_ref() }
    }

    /// Returns `true` if the requested type is the same as `T`
    pub fn is<T: ?Sized + 'static>(&self) -> bool {
        self.type_id() == TypeId::of::<T>()
    }

    /// Try to downcast this `Request` into a reference to the typed
    /// `RequestBuf` object.
    ///
    /// This method will return `None` if `self` was not derived from a
    /// `RequestBuf<'_, T>`.
    fn downcast_buf<T: ?Sized + 'static>(&mut self) -> Option<&mut RequestBuf<'out, T>> {
        if self.is::<T>() {
            unsafe { Some(&mut *(self.buf.as_ptr() as *mut RequestBuf<'out, T>)) }
        } else {
            None
        }
    }

    /// Calls the provided closure with a request for the the type `T`, returning
    /// `Some(&T)` if the request was fulfilled, and `None` otherwise.
    ///
    /// The `ObjectProviderExt` trait provides helper methods specifically for
    /// types implementing `ObjectProvider`.
    pub fn with<T: ?Sized + 'static, F>(f: F) -> Option<&'out T>
    where
        for<'a> F: FnOnce(Request<'a, 'out>) -> ProvideResult<'a, 'out>,
    {
        let mut buf = RequestBuf {
            type_id: TypeId::of::<T>(),
            value: None,
        };
        let _ = f(Request {
            buf: unsafe {
                NonNull::new_unchecked(&mut buf as *mut RequestBuf<'out, T> as *mut TypeId)
            },
            _marker: PhantomData,
        });
        buf.value
    }
}

impl<'r, 'out> fmt::Debug for Request<'r, 'out> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Request")
            .field("type_id", &self.type_id())
            .finish()
    }
}

// Needs to have a known layout so we can do unsafe pointer shenanigans.
#[repr(C)]
struct RequestBuf<'a, T: ?Sized> {
    type_id: TypeId,
    value: Option<&'a T>,
}

/// Trait to provide other objects based on a requested type at runtime.
///
/// See also the [`ObjectProviderExt`] trait which provides the `request` method.
pub trait ObjectProvider {
    /// Provide an object of a given type in response to an untyped request.
    ///
    /// Returns either `Err(FulfilledRequest)` if the request has been
    /// fulfilled, or `Ok(Request)` if the request could not be fulfilled.
    fn provide<'r, 'a>(&'a self, request: Request<'r, 'a>) -> ProvideResult<'r, 'a>;
}

/// Methods supported by all [`ObjectProvider`] implementors.
pub trait ObjectProviderExt {
    /// Request an object of type `T` from an object provider.
    fn request<T: ?Sized + 'static>(&self) -> Option<&T>;
}

impl<O: ?Sized + ObjectProvider> ObjectProviderExt for O {
    fn request<T: ?Sized + 'static>(&self) -> Option<&T> {
        Request::with::<T, _>(|req| self.provide(req))
    }
}

/// Marker type indicating a request has been fulfilled.
pub struct FulfilledRequest(PhantomData<&'static Cell<()>>);

/// Provider method return type.
///
/// Either `Ok(Request)` for an unfulfilled request, or `Err(FulfilledRequest)`
/// if the request was fulfilled.
pub type ProvideResult<'r, 'a> = Result<Request<'r, 'a>, FulfilledRequest>;

#[cfg(test)]
mod test {
    use super::*;
    use std::path::{Path, PathBuf};

    #[test]
    fn basic_context() {
        struct HasContext {
            int: i32,
            path: PathBuf,
        }
        impl ObjectProvider for HasContext {
            fn provide<'r, 'a>(&'a self, request: Request<'r, 'a>) -> ProvideResult<'r, 'a> {
                request
                    .provide::<i32>(&self.int)?
                    .provide::<Path>(&self.path)?
                    .provide::<dyn fmt::Display>(&self.int)
            }
        }

        let provider: &dyn ObjectProvider = &HasContext {
            int: 10,
            path: PathBuf::new(),
        };

        assert_eq!(provider.request::<i32>(), Some(&10));
        assert!(provider.request::<u32>().is_none());
        assert_eq!(
            provider
                .request::<dyn fmt::Display>()
                .map(|d| d.to_string()),
            Some("10".to_owned())
        );
        assert!(provider.request::<dyn fmt::Debug>().is_none());
        assert_eq!(provider.request::<Path>(), Some(Path::new("")));
    }
}
