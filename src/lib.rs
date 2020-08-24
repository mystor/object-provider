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
//! #     fn provide<'a>(&'a self, request: &mut dyn Request<'a>) {
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
//!     fn provide<'a>(&'a self, request: &mut dyn Request<'a>) {
//!         request
//!             .provide_ref::<PathBuf>(&self.path)
//!             .provide_ref::<Path>(&self.path)
//!             .provide_ref::<dyn Debug>(&self.path);
//!     }
//! }
//! ```

use core::any::TypeId;
use core::ptr;

mod private {
    pub struct Private;
    pub trait Sealed {}
}

/// A dynamic request for an object based on its type.
pub unsafe trait Request<'a>: private::Sealed {
    /// /!\ THIS IS NOT PUBLIC API /!\
    ///
    /// Provide a reference with the given type to the request.
    ///
    /// The returned pointer, if non-null, can be cast to point to an `Option<&'a T>`,
    /// where `T` is the type `TypeId` was derived from.
    ///
    /// The lifetime of the returned pointer is the lifetime of `self`.
    #[doc(hidden)]
    fn provide_ref_internal(&mut self, _: private::Private, _type_id: TypeId) -> *mut () {
        ptr::null_mut()
    }

    /// /!\ THIS IS NOT PUBLIC API /!\
    ///
    /// Provide a value with the given type to the request.
    ///
    /// The returned pointer, if non-null, will point to an `Option<T>`, where
    /// `T` is the type `TypeId` was derived from.
    ///
    /// The lifetime of the returned pointer is the lifetime of `self`.
    #[doc(hidden)]
    fn provide_value_internal(&mut self, _: private::Private, _type_id: TypeId) -> *mut () {
        ptr::null_mut()
    }
}

impl<'a> dyn Request<'a> + '_ {
    /// Type-safe wrapper for calling `provide_ref_internal`.
    ///
    /// See `Request::provide_ref_internal`'s documentation for the invariants
    /// being held by this method.
    fn provide_ref_place<'b, T: ?Sized + 'static>(&'b mut self) -> Option<&'b mut Option<&'a T>> {
        let ptr = self.provide_ref_internal(private::Private, TypeId::of::<T>());
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { &mut *(ptr as *mut Option<&'a T>) })
        }
    }

    /// Type-safe wrapper for calling `provide_value_internal`.
    ///
    /// See `Request::provide_value_internal`'s documentation for the invariants
    /// being held by this method.
    fn provide_value_place<'b, T: 'static>(&'b mut self) -> Option<&'b mut Option<T>> {
        let ptr = self.provide_value_internal(private::Private, TypeId::of::<T>());
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { &mut *(ptr as *mut Option<T>) })
        }
    }
}

impl<'a> dyn Request<'a> + '_ {
    /// Provides a reference of type `&'a T` in response to this request.
    ///
    /// If a reference of type `&'a T` has already been provided for this
    /// request, the existing value will be replaced by the newly provided
    /// value.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    pub fn provide_ref<T: ?Sized + 'static>(&mut self, value: &'a T) -> &mut Self {
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
    pub fn provide_ref_with<T, F>(&mut self, cb: F) -> &mut Self
    where
        T: ?Sized + 'static,
        F: FnOnce() -> &'a T,
    {
        if let Some(place) = self.provide_ref_place::<T>() {
            *place = Some(cb());
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
    pub fn provide_value<T: 'static>(&mut self, value: T) -> &mut Self {
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
    pub fn provide_value_with<T, F>(&mut self, cb: F) -> &mut Self
    where
        T: 'static,
        F: FnOnce() -> T,
    {
        if let Some(place) = self.provide_value_place::<T>() {
            *place = Some(cb());
        }
        self
    }
}

/// Trait to provide other objects based on a requested type at runtime.
///
/// See also the [`ObjectProviderExt`] trait which provides the `request_ref` and
/// `request_value` methods.
pub trait ObjectProvider {
    /// Provide an object in response to `request`.
    fn provide<'a>(&'a self, request: &mut dyn Request<'a>);
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
        let mut request = RequestRef::default();
        self.provide(&mut request);
        request.value
    }

    fn request_value<T: 'static>(&self) -> Option<T> {
        let mut request = RequestValue::default();
        self.provide(&mut request);
        request.value
    }
}

/// A request for a reference of type `&'a T`.
///
/// This type implements `Request<'a>`, meaning it can be passed to types
/// expecting `&mut dyn Request<'a>`.
#[derive(Debug)]
pub struct RequestRef<'a, T: ?Sized> {
    /// The value provided to this request, or `None`.
    pub value: Option<&'a T>,
}

impl<'a, T: ?Sized> Default for RequestRef<'a, T> {
    fn default() -> Self {
        RequestRef { value: None }
    }
}

impl<'a, T: ?Sized + 'static> private::Sealed for RequestRef<'a, T> {}

unsafe impl<'a, T: ?Sized + 'static> Request<'a> for RequestRef<'a, T> {
    /// See `Request::provide_ref_internal`'s documentation for the invariants
    /// being upheld by this method.
    #[doc(hidden)]
    fn provide_ref_internal(&mut self, _: private::Private, type_id: TypeId) -> *mut () {
        if type_id == TypeId::of::<T>() {
            &mut self.value as *mut Option<&'a T> as *mut ()
        } else {
            ptr::null_mut()
        }
    }
}

/// A request for a value of type `T`.
///
/// This type implements [`Request`], meaning it can be passed to functions
/// expecting a `&mut dyn Request<'a>` trait object.
#[derive(Debug)]
pub struct RequestValue<T> {
    /// The value provided to this request, or `None`.
    pub value: Option<T>,
}

impl<T> Default for RequestValue<T> {
    fn default() -> Self {
        RequestValue { value: None }
    }
}

impl<T: 'static> private::Sealed for RequestValue<T> {}

unsafe impl<'a, T: 'static> Request<'a> for RequestValue<T> {
    /// See `Request::provide_value_internal`'s documentation for the invariants
    /// being upheld by this method.
    #[doc(hidden)]
    fn provide_value_internal(&mut self, _: private::Private, type_id: TypeId) -> *mut () {
        if type_id == TypeId::of::<T>() {
            &mut self.value as *mut Option<T> as *mut ()
        } else {
            ptr::null_mut()
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::fmt;
    use std::path::{Path, PathBuf};

    #[test]
    fn basic_context() {
        struct HasContext {
            int: i32,
            path: PathBuf,
        }
        impl ObjectProvider for HasContext {
            fn provide<'a>(&'a self, request: &mut dyn Request<'a>) {
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
