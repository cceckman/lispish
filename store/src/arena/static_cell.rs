//! Handles to static data, using atomics only.

#![cfg_attr(feature = "std", allow(unused))]

use core::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    sync::atomic::{AtomicBool, Ordering},
};

use super::Init;

/// A static-safe, lazily-initialized cell.
///
/// None of the existing/builtin cells can be use for no_std static memory allocations.
/// - Cell, RefCell, and OnceCell are not thread-safe.
/// - Mutex is thread-safe, but requires a host.
/// - OnceLock is thread-safe, but has move semantics;
///   we need reference semantics (for "big memory chunks")
///
/// For the big static allocations, we want RefCell semantics, but cross-thread.
///
/// StaticCell implements this by adding an atomic word to the object, and
/// acquiring/releasing it appropriately.
pub struct StaticCell<T> {
    data: UnsafeCell<MaybeUninit<T>>,
    name: &'static str,
    sync: AtomicBool,
}

/// Like RefCell, StaticCell ensures that only one Handle is outstanding at a time.
/// Unlike RefCell, it does so using atomics, and is therefore thread-safe.
unsafe impl<T> Sync for StaticCell<T> {}

/// Error that occurs when a StaticCell is locked for access.
#[derive(Debug)]
pub struct Error {
    name: &'static str,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "cell locked for access: {}", self.name)
    }
}

/// A handle to an object from a SafeStatic.
pub struct Handle<'a, T> {
    data: &'a mut T,
    sync: &'a AtomicBool,
}

impl<T> StaticCell<T>
where
    T: Init,
{
    pub const fn new(name: &'static str) -> Self {
        StaticCell {
            data: UnsafeCell::new(MaybeUninit::uninit()),
            name,
            sync: AtomicBool::new(false),
        }
    }

    /// Get a mutable reference to the stored object;
    /// or, if a reference is already outstanding, generate an error.
    pub fn get(&self) -> Result<Handle<'_, T>, Error> {
        self.sync
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .map_err(|_| Error { name: self.name })?;
        // We assume we haven't initialized it yet:
        let uninit = unsafe { &mut *self.data.get() };
        // Reinitialize it.
        let data = T::init(uninit);
        Ok(Handle {
            data,
            sync: &self.sync,
        })
    }
}

impl<T> Drop for Handle<'_, T> {
    fn drop(&mut self) {
        self.sync.store(true, Ordering::Release);
    }
}

impl<T> AsRef<T> for Handle<'_, T> {
    fn as_ref(&self) -> &T {
        self.data
    }
}

impl<T> AsMut<T> for Handle<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        self.data
    }
}
