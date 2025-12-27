use std::mem::{MaybeUninit, needs_drop, take};
use std::ptr::NonNull;

pub struct ShiftStack<T> {
    buffer: Box<[MaybeUninit<T>]>,
    spare_end: NonNull<MaybeUninit<T>>,
    spare_start: NonNull<MaybeUninit<T>>,
}

impl<T> ShiftStack<T> {
    pub fn new(size: usize) -> Self {
        let mut buffer = Box::new_uninit_slice(size);
        let range = buffer.as_mut_ptr_range();
        Self {
            buffer,
            spare_start: NonNull::new(range.start).unwrap(),
            spare_end: NonNull::new(range.end).unwrap(),
        }
    }

    pub fn push(&mut self, value: T) {
        assert!(self.spare() > 0);
        unsafe {
            self.spare_end = self.spare_end.sub(1);
            self.spare_end.as_mut().write(value);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let top = self.top_uninit()?;
        unsafe {
            let value = top.assume_init_read();
            self.spare_end = self.spare_end.add(1);
            Some(value)
        }
    }

    pub fn top(&self) -> Option<&T> {
        let top = self.top_uninit()?;
        Some(unsafe { top.assume_init_ref() })
    }

    fn top_uninit(&self) -> Option<&MaybeUninit<T>> {
        let top = self.spare_end.as_ptr().cast_const();
        let end = self.buffer.as_ptr_range().end;
        (top < end).then(|| unsafe { self.spare_end.as_ref() })
    }

    pub fn shift(&mut self) {
        let top = self.pop().unwrap();
        unsafe {
            self.spare_start.as_mut().write(top);
            self.spare_start = self.spare_start.add(1);
        }
    }

    pub fn into_boxed_slice(mut self) -> Box<[T]> {
        assert!(self.spare() == 0);
        let buffer = take(&mut self.buffer);
        unsafe { buffer.assume_init() }
    }

    pub fn spare(&self) -> usize {
        let offset = unsafe { self.spare_end.offset_from(self.spare_start) };
        debug_assert!(offset >= 0);
        offset as usize
    }
}

impl<T> Drop for ShiftStack<T> {
    fn drop(&mut self) {
        if needs_drop::<T>() {
            let range = self.buffer.as_mut_ptr_range();

            let mut ptr = range.start;
            while ptr < self.spare_start.as_ptr() {
                unsafe { (*ptr).assume_init_drop() };
                ptr = unsafe { ptr.add(1) };
            }

            let mut ptr = self.spare_end.as_ptr();
            while ptr < range.end {
                unsafe { (*ptr).assume_init_drop() };
                ptr = unsafe { ptr.add(1) };
            }
        }
    }
}
