macro_rules! impl_convert {
    (($from_type:ident, $from_bits:expr), ($(($target_type:ident, $target_bits:expr)),+ $(,)?)) => {
        impl $from_type {
            $(
                paste::paste! {
                    pub fn [<to_ $target_type:lower>](&self) -> $target_type {
                        let a = $target_bits;
                        unimplemented!()
                    }
                }
            )+
        }
    };
}
