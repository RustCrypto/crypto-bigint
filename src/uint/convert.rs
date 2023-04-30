macro_rules! impl_convert {
    ($from_name:ident, $to_name:ident, $from_bits:expr, $to_bits:expr) => {
        impl $from_name {
            pub fn to_$to_name -> $to_name {
                todo!()
            }
        }
     };
}
