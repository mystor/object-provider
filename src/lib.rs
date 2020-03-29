#![cfg_attr(not(test), no_std)]

use core::any::TypeId;
use core::cell::Cell;
use core::fmt;
use core::marker::PhantomData;
use core::ptr::NonNull;

/// A dynamic request for an object based on its type.
pub struct Request<'r, 'out> {
    buf: NonNull<TypeId>,
    _marker: PhantomData<&'r mut &'out Cell<()>>,
}

impl<'r, 'out> Request<'r, 'out> {
    /// Get the type of reference which can be provided in response to this
    /// `Request`.
    pub fn type_id(&self) -> TypeId {
        unsafe { *self.buf.as_ref() }
    }

    /// Tries to provide an object of type `T` in response to this request.
    ///
    /// Returns `None` if the value was successfully provided, and `Some(self)`
    /// if there was a type mismatch.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    ///
    /// # Panic
    ///
    /// This method will panic if a value has already been provided.
    pub fn try_provide<T: ?Sized + 'static>(self, value: &'out T) -> Option<Self> {
        self.try_provide_with(|| value)
    }

    /// Tries to provide an object of type `T` in response to this request.
    ///
    /// Returns `None` if the value was successfully provided, and `Some(self)`
    /// if there was a type mismatch.
    ///
    /// This method can be chained within `provide` implementations to concisely
    /// provide multiple objects.
    ///
    /// # Panic
    ///
    /// This method will panic if a value has already been provided.
    pub fn try_provide_with<T: ?Sized + 'static, F>(mut self, cb: F) -> Option<Self>
    where
        F: FnOnce() -> &'out T,
    {
        match self.downcast::<T>() {
            Some(this) => {
                assert!(this.value.is_none(), "a value has already been provided");
                this.value = Some(cb());
                None
            }
            None => Some(self),
        }
    }

    /// Try to downcast this `Request` into a reference to the typed
    /// `RequestBuf` object.
    ///
    /// This method will return `None` if `self` was not derived from a
    /// `RequestBuf<'_, T>`.
    pub(crate) fn downcast<T: ?Sized + 'static>(&mut self) -> Option<&mut RequestBuf<'out, T>> {
        if self.type_id() == TypeId::of::<T>() {
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
    pub fn with_request<T: ?Sized + 'static, F>(f: F) -> Option<&'out T>
    where
        for<'a> F: FnOnce(Request<'a, 'out>) -> Option<Request<'a, 'out>>,
    {
        let mut buf = RequestBuf {
            type_id: TypeId::of::<T>(),
            value: None,
        };
        f(Request {
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

/// An object which can provide other objects based on the requested type.
///
/// # Object Safety
///
/// The type of the passed-in request is erased using the `Request` type,
/// meaning this trait is object-safe.
pub trait ObjectProvider {
    /// Provide an object of a given type in response to an untyped request.
    ///
    /// Returns `None` when a value has been `provide`-ed to the `request`, and
    /// `Some(request)` if the request hasn't been fulfilled yet.
    ///
    /// Consumers generally won't want to call this method. Instead use the
    /// [`ObjectProviderExt::request`] method.
    fn provide<'r, 'a>(&'a self, request: Request<'r, 'a>) -> Option<Request<'r, 'a>>;
}

/// Common extension methods implemented for all `ObjectProvider` instances.
pub trait ObjectProviderExt {
    /// Request an object of type `T` from an object provider.
    fn request<T: ?Sized + 'static>(&self) -> Option<&T>;
}

impl<O: ?Sized + ObjectProvider> ObjectProviderExt for O {
    fn request<T: ?Sized + 'static>(&self) -> Option<&T> {
        Request::with_request::<T, _>(|req| self.provide(req))
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
            fn provide<'r, 'a>(&'a self, request: Request<'r, 'a>) -> Option<Request<'r, 'a>> {
                request
                    .try_provide::<i32>(&self.int)?
                    .try_provide::<Path>(&self.path)?
                    .try_provide::<dyn fmt::Display>(&self.int)
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
