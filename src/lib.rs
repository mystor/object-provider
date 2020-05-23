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
//! #             .provide_ref::<PathBuf>(&self.path)
//! #             .provide_ref::<Path>(&self.path)
//! #             .provide_ref::<dyn Debug>(&self.path);
//! #     }
//! # }
//! # let my_path = Path::new("hello/world");
//! # let my_provider = MyProvider { path: my_path.to_owned() };
//! let provider: &dyn ObjectProvider;
//! # provider = &my_provider;
//!
//! // It's possible to request concrete types like `PathBuf`
//! let path_buf = provider.request_ref::<PathBuf>().unwrap();
//! assert_eq!(path_buf, my_path);
//!
//! // Requesting `!Sized` types, like slices and trait objects, is also supported.
//! let path = provider.request_ref::<Path>().unwrap();
//! assert_eq!(path, my_path);
//!
//! let debug = provider.request_ref::<dyn Debug>().unwrap();
//! assert_eq!(
//!     format!("{:?}", debug),
//!     format!("{:?}", my_path),
//! );
//!
//! // Types or interfaces not explicitly provided return `None`.
//! assert!(provider.request_ref::<i32>().is_none());
//! assert!(provider.request_ref::<dyn AsRef<Path>>().is_none());
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
//!             .provide_ref::<PathBuf>(&self.path)
//!             .provide_ref::<Path>(&self.path)
//!             .provide_ref::<dyn Debug>(&self.path);
//!     }
//! }
//! ```

use core::any::TypeId;
use core::fmt;
use core::marker::{PhantomData, PhantomPinned};
use core::pin::Pin;

struct ReqRef<T: ?Sized + 'static>(&'static T);
struct ReqVal<T: 'static>(T);

/// A dynamic request for an object based on its type.
#[repr(C)]
pub struct Request<'a> {
    type_id: TypeId,
    _pinned: PhantomPinned,
    _marker: PhantomData<&'a ()>,
}

impl<'a> Request<'a> {
    /// Provides a reference of type `&'a T` in response to this request.
    ///
    /// If a reference of type `&'a T` has already been provided for this
    /// request, the existing value will be replaced by the newly provided
    /// value.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide_ref<T: ?Sized + 'static>(self: Pin<&mut Self>, value: &'a T) -> Pin<&mut Self> {
        self.provide_ref_with(|| value)
    }

    /// Lazily provides a reference of type `&'a T` in response to this request.
    ///
    /// If a reference of type `&'a T` has already been provided for this
    /// request, the existing value will be replaced by the newly provided
    /// value.
    ///
    /// The passed closure is only called if the value will be successfully
    /// provided.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide_ref_with<T: ?Sized + 'static, F>(
        mut self: Pin<&mut Self>,
        cb: F,
    ) -> Pin<&mut Self>
    where
        F: FnOnce() -> &'a T,
    {
        if self.is_ref::<T>() {
            // safety: `self.is_ref::<T>()` ensured the data field is `&'a T`.
            unsafe {
                *self.as_mut().downcast_unchecked::<&'a T>() = Some(cb());
            }
        }
        self
    }

    /// Provides an value of type `T` in response to this request.
    ///
    /// If a value of type `T` has already been provided for this request, the
    /// existing value will be replaced by the newly provided value.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide_value<T: 'static>(self: Pin<&mut Self>, value: T) -> Pin<&mut Self> {
        self.provide_value_with(|| value)
    }

    /// Lazily provides a value of type `T` in response to this request.
    ///
    /// If a value of type `T` has already been provided for this request, the
    /// existing value will be replaced by the newly provided value.
    ///
    /// The passed closure is only called if the value will be successfully
    /// provided.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide_value_with<T: 'static, F>(mut self: Pin<&mut Self>, cb: F) -> Pin<&mut Self>
    where
        F: FnOnce() -> T,
    {
        if self.is_value::<T>() {
            // safety: `self.is_value::<T>()` ensured the data field is `T`.
            unsafe {
                *self.as_mut().downcast_unchecked::<T>() = Some(cb());
            }
        }
        self
    }

    /// Returns `true` if the requested type is `&'a T`
    pub fn is_ref<T: ?Sized + 'static>(&self) -> bool {
        self.type_id == TypeId::of::<ReqRef<T>>()
    }

    /// Returns `true` if the requested type is `T`
    pub fn is_value<T: 'static>(&self) -> bool {
        self.type_id == TypeId::of::<ReqVal<T>>()
    }

    // internal implementation detail - performs an unchecked downcast.
    unsafe fn downcast_unchecked<T>(self: Pin<&mut Self>) -> &mut Option<T> {
        let ptr = self.get_unchecked_mut() as *mut Self as *mut RequestBuf<'a, T>;
        &mut (*ptr).value
    }

    /// Calls the provided closure with a request for the the type `&'a T`,
    /// returning `Some(&T)` if the request was fulfilled, and `None` otherwise.
    ///
    /// The `ObjectProviderExt` trait provides helper methods specifically for
    /// types implementing `ObjectProvider`.
    pub fn request_ref<T: ?Sized + 'static, F>(f: F) -> Option<&'a T>
    where
        F: FnOnce(Pin<&mut Request<'a>>),
    {
        let mut buf = RequestBuf::for_ref();
        // safety: We never move `buf` after creating `pinned`.
        let mut pinned = unsafe { Pin::new_unchecked(&mut buf) };
        f(pinned.as_mut().request());
        pinned.take()
    }

    /// Calls the provided closure with a request for the the type `T`,
    /// returning `Some(T)` if the request was fulfilled, and `None` otherwise.
    ///
    /// The `ObjectProviderExt` trait provides helper methods specifically for
    /// types implementing `ObjectProvider`.
    pub fn request_value<T: 'static, F>(f: F) -> Option<T>
    where
        F: FnOnce(Pin<&mut Request<'a>>),
    {
        let mut buf = RequestBuf::for_value();
        // safety: We never move `buf` after creating `pinned`.
        let mut pinned = unsafe { Pin::new_unchecked(&mut buf) };
        f(pinned.as_mut().request());
        pinned.take()
    }
}

impl<'a> fmt::Debug for Request<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Request")
            .field("type_id", &self.type_id)
            .finish()
    }
}

/// Low level buffer API used to create typed object requests.
///
/// Due to a heavy dependency on [`Pin`], this type is inconvenient to use
/// directly. Prefer using the [`ObjectProviderExt`] trait and [`Request::with`]
/// APIs when possible.
// Needs to have a known layout so we can do unsafe pointer shenanigans.
#[repr(C)]
#[derive(Debug)]
pub struct RequestBuf<'a, T> {
    request: Request<'a>,
    value: Option<T>,
}

impl<'a, T: ?Sized + 'static> RequestBuf<'a, &'a T> {
    /// Create a new `RequestBuf` object.
    ///
    /// This type must be pinned before it can be used.
    pub fn for_ref() -> Self {
        // safety: ReqRef is a marker type for `&'a T`
        unsafe { Self::new_internal(TypeId::of::<ReqRef<T>>()) }
    }
}

impl<'a, T: 'static> RequestBuf<'a, T> {
    /// Create a new `RequestBuf` object.
    ///
    /// This type must be pinned before it can be used.
    pub fn for_value() -> Self {
        // safety: ReqVal is a marker type for `T`
        unsafe { Self::new_internal(TypeId::of::<ReqVal<T>>()) }
    }
}

impl<'a, T> RequestBuf<'a, T> {
    unsafe fn new_internal(type_id: TypeId) -> Self {
        RequestBuf {
            request: Request {
                type_id,
                _pinned: PhantomPinned,
                _marker: PhantomData,
            },
            value: None,
        }
    }

    /// Get the untyped `Request` reference for this `RequestBuf`.
    pub fn request(self: Pin<&mut Self>) -> Pin<&mut Request<'a>> {
        // safety: projecting Pin onto our `request` field.
        unsafe { self.map_unchecked_mut(|this| &mut this.request) }
    }

    /// Take a value previously provided to this `RequestBuf`.
    pub fn take(self: Pin<&mut Self>) -> Option<T> {
        // safety: we don't project Pin onto our `value` field.
        unsafe { self.get_unchecked_mut().value.take() }
    }
}

/// Trait to provide other objects based on a requested type at runtime.
///
/// See also the [`ObjectProviderExt`] trait which provides the `request` method.
pub trait ObjectProvider {
    /// Provide an object of a given type in response to an untyped request.
    fn provide<'a>(&'a self, request: Pin<&mut Request<'a>>);
}

/// Methods supported by all [`ObjectProvider`] implementors.
pub trait ObjectProviderExt {
    /// Request a reference of type `&T` from an object provider.
    fn request_ref<T: ?Sized + 'static>(&self) -> Option<&T>;

    /// Request an owned value of type `T` from an object provider.
    fn request_value<T: 'static>(&self) -> Option<T>;
}

impl<O: ?Sized + ObjectProvider> ObjectProviderExt for O {
    fn request_ref<T: ?Sized + 'static>(&self) -> Option<&T> {
        Request::request_ref::<T, _>(|req| self.provide(req))
    }

    fn request_value<T: 'static>(&self) -> Option<T> {
        Request::request_value::<T, _>(|req| self.provide(req))
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
                    .provide_ref::<i32>(&self.int)
                    .provide_ref::<Path>(&self.path)
                    .provide_ref::<dyn fmt::Display>(&self.int)
                    .provide_value::<i32>(self.int);
            }
        }

        let provider: &dyn ObjectProvider = &HasContext {
            int: 10,
            path: PathBuf::new(),
        };

        assert_eq!(provider.request_ref::<i32>(), Some(&10));
        assert_eq!(provider.request_value::<i32>(), Some(10));
        assert!(provider.request_ref::<u32>().is_none());
        assert_eq!(
            provider
                .request_ref::<dyn fmt::Display>()
                .map(|d| d.to_string()),
            Some("10".to_owned())
        );
        assert!(provider.request_ref::<dyn fmt::Debug>().is_none());
        assert_eq!(provider.request_ref::<Path>(), Some(Path::new("")));
    }
}
