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
//!             .provide_ref::<dyn Debug>(&self.path)
//!             .provide_value_with::<String, _>(|| {
//!                 self.path.to_string_lossy().into_owned()
//!             });
//!     }
//! }
//! ```

use core::any::TypeId;
use core::marker::PhantomData;

mod private {
    pub trait Response<'a>: 'a {}
}

/// A response to a ref request.
struct RefResponse<'a, T: ?Sized + 'static>(Option<&'a T>);
impl<'a, T: ?Sized + 'static> private::Response<'a> for RefResponse<'a, T> {}

/// A response to a value request.
struct ValueResponse<T: 'static>(Option<T>);
impl<'a, T: 'static> private::Response<'a> for ValueResponse<T> {}

/// A dynamic request for an object based on its type.
pub struct Request<'a, R = dyn private::Response<'a>>
where
    R: ?Sized + private::Response<'a>,
{
    marker: PhantomData<&'a ()>,

    /// A `TypeId` marker for the type stored in `R`.
    ///
    /// Will be the TypeId of either `RefResponse<'static, T>` or
    /// `ValueResponse<T>`.
    type_id: TypeId,

    /// A type erased `RefResponse` or `ValueResponse` containing the response
    /// value.
    response: R,
}

impl<'a> Request<'a> {
    /// Perform a checked downcast of `response` to `Option<&'a T>`
    fn downcast_ref_response<'b, T: ?Sized + 'static>(
        &'b mut self,
    ) -> Option<&'b mut RefResponse<'a, T>> {
        if self.is_ref::<T>() {
            // safety: If `self.is_ref::<T>()` returns true, `response` must be
            // of the correct type. This is enforced by the private `type_id`
            // field.
            Some(unsafe { &mut *(&mut self.response as *mut _ as *mut RefResponse<'a, T>) })
        } else {
            None
        }
    }

    /// Perform a checked downcast of `response` to `Option<T>`
    fn downcast_value_response<'b, T: 'static>(&'b mut self) -> Option<&'b mut ValueResponse<T>> {
        if self.is_value::<T>() {
            // safety: If `self.is_value::<T>()` returns true, `response` must
            // be of the correct type. This is enforced by the private `type_id`
            // field.
            Some(unsafe { &mut *(&mut self.response as *mut _ as *mut ValueResponse<T>) })
        } else {
            None
        }
    }

    /// Provides a reference of type `&'a T` in response to this request.
    ///
    /// If a reference of type `&'a T` has already been provided for this
    /// request, or if the request is for a different type, this call will be
    /// ignored.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    ///
    /// # Example
    ///
    /// ```
    /// # use object_provider::{ObjectProvider, Request};
    /// # use std::fmt;
    /// struct MyProvider {
    ///     name: String,
    /// }
    ///
    /// impl ObjectProvider for MyProvider {
    ///     fn provide<'a>(&'a self, request: &mut Request<'a>) {
    ///         request
    ///             .provide_ref::<Self>(&self)
    ///             .provide_ref::<String>(&self.name)
    ///             .provide_ref::<str>(&self.name)
    ///             .provide_ref::<dyn fmt::Display>(&self.name);
    ///     }
    /// }
    /// ```
    pub fn provide_ref<T: ?Sized + 'static>(&mut self, value: &'a T) -> &mut Self {
        self.provide_ref_with(|| value)
    }

    /// Lazily provides a reference of type `&'a T` in response to this request.
    ///
    /// If a reference of type `&'a T` has already been provided for this
    /// request, or if the request is for a different type, this call will be
    /// ignored.
    ///
    /// The passed closure is only called if the value will be successfully
    /// provided.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    ///
    /// # Example
    ///
    /// ```
    /// # use object_provider::{ObjectProvider, Request};
    /// # fn expensive_condition() -> bool { true }
    /// struct MyProvider {
    ///     a: String,
    ///     b: String,
    /// }
    ///
    /// impl ObjectProvider for MyProvider {
    ///     fn provide<'a>(&'a self, request: &mut Request<'a>) {
    ///         request.provide_ref_with::<String, _>(|| {
    ///             if expensive_condition() {
    ///                 &self.a
    ///             } else {
    ///                 &self.b
    ///             }
    ///         });
    ///     }
    /// }
    /// ```
    pub fn provide_ref_with<T: ?Sized + 'static, F>(&mut self, cb: F) -> &mut Self
    where
        F: FnOnce() -> &'a T,
    {
        if let Some(RefResponse(response @ None)) = self.downcast_ref_response::<T>() {
            *response = Some(cb());
        }
        self
    }

    /// Provides an value of type `T` in response to this request.
    ///
    /// If a value of type `T` has already been provided for this request, or if
    /// the request is for a different type, this call will be ignored.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    ///
    /// # Example
    ///
    /// ```
    /// # use object_provider::{ObjectProvider, Request};
    /// struct MyProvider {
    ///     count: u32,
    /// }
    ///
    /// impl ObjectProvider for MyProvider {
    ///     fn provide<'a>(&'a self, request: &mut Request<'a>) {
    ///         request
    ///             .provide_value::<u32>(self.count)
    ///             .provide_value::<&'static str>("hello, world!");
    ///     }
    /// }
    /// ```
    pub fn provide_value<T: 'static>(&mut self, value: T) -> &mut Self {
        self.provide_value_with(|| value)
    }

    /// Lazily provides a value of type `T` in response to this request.
    ///
    /// If a value of type `T` has already been provided for this request, or if
    /// the request is for a different type, this call will be ignored.
    ///
    /// The passed closure is only called if the value will be successfully
    /// provided.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    ///
    /// # Example
    ///
    /// ```
    /// # use object_provider::{ObjectProvider, Request};
    /// struct MyProvider {
    ///     count: u32,
    /// }
    ///
    /// impl ObjectProvider for MyProvider {
    ///     fn provide<'a>(&'a self, request: &mut Request<'a>) {
    ///         request
    ///             .provide_value_with::<u32, _>(|| self.count / 10)
    ///             .provide_value_with::<String, _>(|| format!("{}", self.count));
    ///     }
    /// }
    /// ```
    pub fn provide_value_with<T: 'static, F>(&mut self, cb: F) -> &mut Self
    where
        F: FnOnce() -> T,
    {
        if let Some(ValueResponse(response @ None)) = self.downcast_value_response::<T>() {
            *response = Some(cb());
        }
        self
    }

    /// Returns `true` if the requested type is `&'a T`
    pub fn is_ref<T: ?Sized + 'static>(&self) -> bool {
        self.type_id == TypeId::of::<RefResponse<'static, T>>()
    }

    /// Returns `true` if the requested type is `T`
    pub fn is_value<T: 'static>(&self) -> bool {
        self.type_id == TypeId::of::<ValueResponse<T>>()
    }

    /// Calls the provided closure with a request for the the type `&'a T`,
    /// returning `Some(&T)` if the request was fulfilled, and `None` otherwise.
    ///
    /// The `ObjectProviderExt` trait provides helper methods specifically for
    /// types implementing `ObjectProvider`.
    ///
    /// # Example
    ///
    /// ```
    /// # use object_provider::Request;
    /// let response: Option<&str> = Request::request_ref(|request| {
    ///     // ...
    ///     request.provide_ref::<str>("hello, world");
    /// });
    /// assert_eq!(response, Some("hello, world"));
    /// ```
    pub fn request_ref<T: ?Sized + 'static, F>(cb: F) -> Option<&'a T>
    where
        F: FnOnce(&mut Request<'a>),
    {
        let mut request = Request::new_ref();
        cb(&mut request);
        request.response.0
    }

    /// Calls the provided closure with a request for the the type `T`,
    /// returning `Some(T)` if the request was fulfilled, and `None` otherwise.
    ///
    /// The `ObjectProviderExt` trait provides helper methods specifically for
    /// types implementing `ObjectProvider`.
    ///
    /// # Example
    ///
    /// ```
    /// # use object_provider::Request;
    /// let response: Option<i32> = Request::request_value(|request| {
    ///     // ...
    ///     request.provide_value::<i32>(5);
    /// });
    /// assert_eq!(response, Some(5));
    /// ```
    pub fn request_value<T: 'static, F>(cb: F) -> Option<T>
    where
        F: FnOnce(&mut Request<'a>),
    {
        let mut request = Request::new_value();
        cb(&mut request);
        request.response.0
    }
}

impl<'a, T: ?Sized + 'static> Request<'a, RefResponse<'a, T>> {
    /// Create a new reference request object.
    ///
    /// The returned value will unsize to `Request<'a>`, and can be passed to
    /// functions accepting it as an argument to request `&'a T` references.
    fn new_ref() -> Self {
        // safety: Initializes `type_id` to `RefResponse<'static, T>`, which
        // corresponds to the response type `RefResponse<'a, T>`.
        Request {
            marker: PhantomData,
            type_id: TypeId::of::<RefResponse<'static, T>>(),
            response: RefResponse(None),
        }
    }
}

impl<T: 'static> Request<'_, ValueResponse<T>> {
    /// Create a new value request object.
    ///
    /// The returned value will unsize to `Request<'a>`, and can be passed to
    /// functions accepting it as an argument to request `T` values.
    fn new_value() -> Self {
        // safety: Initializes `type_id` to `ValueResponse<T>`, which
        // corresponds to the response type `ValueResponse<T>`.
        Request {
            marker: PhantomData,
            type_id: TypeId::of::<ValueResponse<T>>(),
            response: ValueResponse(None),
        }
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
        Request::request_ref(|request| self.provide(request))
    }

    fn request_value<T: 'static>(&self) -> Option<T> {
        Request::request_value(|request| self.provide(request))
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
