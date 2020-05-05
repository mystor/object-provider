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
//! # use std::pin::Pin;
//! # struct MyProvider {
//! #     path: PathBuf,
//! # }
//! # impl ObjectProvider for MyProvider {
//! #     fn provide<'a>(&'a self, request: Pin<&mut Request<'a>>) {
//! #         request
//! #             .provide::<PathBuf>(&self.path)
//! #             .provide::<Path>(&self.path)
//! #             .provide::<dyn Debug>(&self.path);
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
//! # use std::pin::Pin;
//! struct MyProvider {
//!     path: PathBuf,
//! }
//!
//! impl ObjectProvider for MyProvider {
//!     fn provide<'a>(&'a self, request: Pin<&mut Request<'a>>) {
//!         request
//!             .provide::<PathBuf>(&self.path)
//!             .provide::<Path>(&self.path)
//!             .provide::<dyn Debug>(&self.path);
//!     }
//! }
//! ```

use core::any::TypeId;
use core::fmt;
use core::marker::{PhantomData, PhantomPinned};
use core::pin::Pin;

/// A dynamic request for an object based on its type.
///
/// `'out` is the lifetime of the requested reference.
#[repr(C)]
pub struct Request<'out> {
    type_id: TypeId,
    _pinned: PhantomPinned,
    _marker: PhantomData<&'out ()>,
}

impl<'out> Request<'out> {
    /// Provides an object of type `T` in response to this request.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide<T: ?Sized + 'static>(self: Pin<&mut Self>, value: &'out T) -> Pin<&mut Self> {
        self.provide_with(|| value)
    }

    /// Lazily provides an object of type `T` in response to this request.
    ///
    /// The passed closure is only called if the value will be successfully
    /// provided.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide_with<T: ?Sized + 'static, F>(mut self: Pin<&mut Self>, cb: F) -> Pin<&mut Self>
    where
        F: FnOnce() -> &'out T,
    {
        if let Some(buf) = self.as_mut().downcast_buf::<T>() {
            debug_assert!(
                buf.is_none(),
                "Multiple requests to a `RequestBuf` were acquired?"
            );
            *buf = Some(cb());
        }
        self
    }

    /// Get the `TypeId` of the requested type.
    pub fn type_id(&self) -> TypeId {
        self.type_id
    }

    /// Returns `true` if the requested type is the same as `T`
    pub fn is<T: ?Sized + 'static>(&self) -> bool {
        self.type_id() == TypeId::of::<T>()
    }

    /// Try to downcast this `Request` into a reference to the typed
    /// `RequestBuf` object, and access the trailing `Option<&'out T>`.
    ///
    /// This method will return `None` if `self` is not the prefix of a
    /// `RequestBuf<'_, T>`.
    fn downcast_buf<T: ?Sized + 'static>(self: Pin<&mut Self>) -> Option<&mut Option<&'out T>> {
        if self.is::<T>() {
            unsafe {
                // Safety: `self` is pinned, meaning it exists as the first
                // field within our `RequestBuf`. As the type matches, this
                // downcast is sound.
                let ptr = self.get_unchecked_mut() as *mut Self as *mut RequestBuf<'out, T>;
                Some(&mut (*ptr).value)
            }
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
        F: FnOnce(Pin<&mut Request<'out>>),
    {
        let mut buf = RequestBuf {
            request: Request {
                type_id: TypeId::of::<T>(),
                _pinned: PhantomPinned,
                _marker: PhantomData,
            },
            value: None,
        };
        unsafe {
            // safety: We never move `buf` or `buf.request`.
            f(Pin::new_unchecked(&mut buf.request));
        }
        buf.value
    }
}

impl<'out> fmt::Debug for Request<'out> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Request")
            .field("type_id", &self.type_id())
            .finish()
    }
}

// Needs to have a known layout so we can do unsafe pointer shenanigans.
#[repr(C)]
struct RequestBuf<'a, T: ?Sized> {
    request: Request<'a>,
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
    fn provide<'a>(&'a self, request: Pin<&mut Request<'a>>);
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
            fn provide<'a>(&'a self, request: Pin<&mut Request<'a>>) {
                request
                    .provide::<i32>(&self.int)
                    .provide::<Path>(&self.path)
                    .provide::<dyn fmt::Display>(&self.int);
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
