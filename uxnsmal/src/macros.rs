#[macro_export]
macro_rules! bug {
    ($($arg:tt)+) => {
        panic!("this is a bug: {}", format_args!($($arg)+))
    };
}
