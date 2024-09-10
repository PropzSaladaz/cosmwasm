#[macro_export]
macro_rules! print_with_thread_id {
    ($($arg:tt)*) => {
        eprintln!("[{:?}] {}", std::thread::current().id(), format_args!($($arg)*));
    };
}