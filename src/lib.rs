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
//! #     fn provide<'a>(&'a self, request: &mut Request<'a>) {
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
//!     fn provide<'a>(&'a self, request: &mut Request<'a>) {
//!         request
//!             .provide_ref::<PathBuf>(&self.path)
//!             .provide_ref::<Path>(&self.path)
//!             .provide_ref::<dyn Debug>(&self.path);
//!     }
//! }
//! ```

use core::any::TypeId;
use core::marker::PhantomData;

mod private {
    pub trait Response {}
    impl<T> Response for Option<T> {}
}

/// When used by `Request`, `TypeId::of::<RefMarker<T>>()` indicates that
/// `response` is of type `Option<&'a T>`.
struct RefMarker<T: ?Sized + 'static>(T);

/// When used by `Request`, `TypeId::of::<ValueMarker<T>>()` indicates that
/// `response` is of type `Option<T>`.
struct ValueMarker<T: 'static>(T);

/// A dynamic request for an object based on its type.
pub struct Request<'a, R = dyn private::Response + 'a>
where
    R: ?Sized + private::Response,
{
    marker: PhantomData<&'a ()>,

    /// A `TypeId` marker for the type stored in `R`.
    ///
    /// Will be the TypeId of either `RefMarker<T>` or `ValueMarker<T>`.
    type_id: TypeId,

    /// A (potentially type-erased) `Option<T>` containing the response value.
    ///
    /// Will be either `Option<&'a T>` if `type_id` is `RefMarker<T>`, or
    /// `Option<T>` if `type_id` is `ValueMarker<T>`.
    response: R,
}

impl<'a> Request<'a> {
    /// Perform a checked downcast of `response` to `Option<&'a T>`
    fn downcast_ref_response<'b, T: ?Sized + 'static>(
        &'b mut self,
    ) -> Option<&'b mut Option<&'a T>> {
        if self.is_ref::<T>() {
            // safety: If `self.is_ref::<T>()` returns true, `response` must be
            // of the correct type. This is enforced by the private `type_id`
            // field.
            Some(unsafe { &mut *(&mut self.response as *mut _ as *mut Option<&'a T>) })
        } else {
            None
        }
    }

    /// Perform a checked downcast of `response` to `Option<T>`
    fn downcast_value_response<'b, T: 'static>(&'b mut self) -> Option<&'b mut Option<T>> {
        if self.is_value::<T>() {
            // safety: If `self.is_value::<T>()` returns true, `response` must
            // be of the correct type. This is enforced by the private `type_id`
            // field.
            Some(unsafe { &mut *(&mut self.response as *mut _ as *mut Option<T>) })
        } else {
            None
        }
    }

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
    pub fn provide_ref_with<T: ?Sized + 'static, F>(&mut self, cb: F) -> &mut Self
    where
        F: FnOnce() -> &'a T,
    {
        if let Some(response) = self.downcast_ref_response::<T>() {
            *response = Some(cb());
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
    pub fn provide_value_with<T: 'static, F>(&mut self, cb: F) -> &mut Self
    where
        F: FnOnce() -> T,
    {
        if let Some(response) = self.downcast_value_response::<T>() {
            *response = Some(cb());
        }
        self
    }

    /// Returns `true` if the requested type is `&'a T`
    pub fn is_ref<T: ?Sized + 'static>(&self) -> bool {
        self.type_id == TypeId::of::<RefMarker<T>>()
    }

    /// Returns `true` if the requested type is `T`
    pub fn is_value<T: 'static>(&self) -> bool {
        self.type_id == TypeId::of::<ValueMarker<T>>()
    }
}

impl<'a, T: ?Sized + 'static> Request<'a, Option<&'a T>> {
    /// Create a new reference request object.
    ///
    /// The returned value will unsize to `Request<'a>`, and can be passed to
    /// functions accepting it as an argument to request `&'a T` references.
    pub fn new_ref() -> Self {
        // safety: Initializes `type_id` to `RefMarker<T>`, which corresponds to
        // the response type `Option<&'a T>`.
        Request {
            marker: PhantomData,
            type_id: TypeId::of::<RefMarker<T>>(),
            response: None,
        }
    }
}

impl<T: 'static> Request<'_, Option<T>> {
    /// Create a new value request object.
    ///
    /// The returned value will unsize to `Request<'a>`, and can be passed to
    /// functions accepting it as an argument to request `T` values.
    pub fn new_value() -> Self {
        // safety: Initializes `type_id` to `ValueMarker<T>`, which corresponds
        // to the response type `Option<T>`.
        Request {
            marker: PhantomData,
            type_id: TypeId::of::<ValueMarker<T>>(),
            response: None,
        }
    }
}

impl<T> Request<'_, Option<T>> {
    /// Extract the response from this request object, consuming it.
    pub fn into_response(self) -> Option<T> {
        self.response
    }
}

/// Trait to provide other objects based on a requested type at runtime.
///
/// See also the [`ObjectProviderExt`] trait which provides the `request_ref` and
/// `request_value` methods.
pub trait ObjectProvider {
    /// Provide an object in response to `request`.
    fn provide<'a>(&'a self, request: &mut Request<'a>);
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
        let mut request = Request::new_ref();
        self.provide(&mut request);
        request.into_response()
    }

    fn request_value<T: 'static>(&self) -> Option<T> {
        let mut request = Request::new_value();
        self.provide(&mut request);
        request.into_response()
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
            fn provide<'a>(&'a self, request: &mut Request<'a>) {
                request
                    .provide_ref::<i32>(&self.int)
                    .provide_ref::<Path>(&self.path)
                    .provide_ref::<dyn fmt::Display>(&self.int)
                    .provide_value::<i32>(self.int)
                    .provide_value_with::<i64, _>(|| self.int as i64);
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
