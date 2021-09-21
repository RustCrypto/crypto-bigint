# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.2.10 (2021-09-21)
### Added
- `ArrayDecoding` trait ([#12])
- `NonZero` wrapper ([#13], [#16])
- Impl `Div`/`Rem` for `NonZero<UInt>` ([#14])

[#12]: https://github.com/RustCrypto/formats/pull/12
[#13]: https://github.com/RustCrypto/formats/pull/13
[#14]: https://github.com/RustCrypto/formats/pull/14
[#16]: https://github.com/RustCrypto/formats/pull/16

## 0.2.9 (2021-09-16)
### Added
- `UInt::sqrt` ([#9])

### Changed
- Make `UInt` division similar to other interfaces ([#8])

[#8]: https://github.com/RustCrypto/formats/pull/8
[#9]: https://github.com/RustCrypto/formats/pull/9

## 0.2.8 (2021-09-14) [YANKED]
### Added
- Implement constant-time division and modulo operations

### Changed
- Moved from RustCrypto/utils to RustCrypto/crypto-bigint repo ([#2])

[#2]: https://github.com/RustCrypto/formats/pull/2

## 0.2.7 (2021-09-12)
### Added
- `UInt::shl_vartime` 

### Fixed
- `add_mod` overflow handling

## 0.2.6 (2021-09-08)
### Added
- `Integer` trait
- `ShrAssign` impl for `UInt`
- Recursive Length Prefix (RLP) encoding support for `UInt`

## 0.2.5 (2021-09-02)
### Fixed
- `ConditionallySelectable` impl for `UInt`

## 0.2.4 (2021-08-23) [YANKED]
### Added
- Expose `limb` module
- `[limb::Inner; LIMBS]` conversions for `UInt`
- Bitwise right shift support for `UInt` ([#586], [#590])

## 0.2.3 (2021-08-16) [YANKED]
### Fixed
- `UInt::wrapping_mul`

### Added
- Implement the `Hash` trait for `UInt` and `Limb`

## 0.2.2 (2021-06-26) [YANKED]
### Added
- `Limb::is_odd` and `UInt::is_odd`
- `UInt::new`
- `rand` feature

### Changed
- Deprecate `LIMB_BYTES` constant
- Make `Limb`'s `Inner` value public

## 0.2.1 (2021-06-21) [YANKED]
### Added
- `Limb` newtype
- Target-specific rustdocs

## 0.2.0 (2021-06-07) [YANKED]
### Added
- `ConstantTimeGreater`/`ConstantTimeLess` impls for UInt
- `From` conversions between `UInt` and limb arrays
- `zeroize` feature
- Additional `ArrayEncoding::ByteSize` bounds
- `UInt::into_limbs`
- `Encoding` trait

### Removed
- `NumBits`/`NumBytes` traits; use `Encoding` instead

## 0.1.0 (2021-05-30)
- Initial release
