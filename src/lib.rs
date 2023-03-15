//! Parses a RISC-V target string like `riscv32imac-unknown-none-elf`.
//!
//! # RISC-V ISA Naming Details
//!
//! The architecture name communicates the native bit-width of an integer, as well as the set of instructions available for software to use.
//!
//! For example, `riscv32im` means a 32-bit processor with the base `i`nteger and extended integer `m`ultiplication & division instructions, and `riscv64gc` targets a 64-bit processor that offers the `g`eneral-purpose instruction set (composed from the base integer set and a number of independent extensions), as well as support for `c`ompressed instructions.
//!
//! For more details, see [ISA Naming Conventions](https://f004.backblazeb2.com/file/shared-sethp/riscv-spec-20191213-2.pdf#chapter.27), chapter #27 of the version of the RISC-V spec ratified in late 2019.
//!
//! ## Instruction Sets
//!
//! TODO docs
//!
//!
//! Note that the RISC-V standard defines the names as case-insensitive, so `A` is the same as `a`, and `Zicsr` is the same as `ziCSR`.
//!
//! ## Notable differences from the standard
//!
//! 1. This package is happy to accept non-standard orderings (like `riscv32mi`), but will only emit the standard ordering (i.e. `riscv32im`). See the spec for the full ordering rules.
//! 2. The standard defines the prefix for a named RISC-V instruction set to be `rv`, but LLVM (and thus, `rustc`) uses `riscv`: this package accepts the latter (`riscv32imac`) but not the former (`rv32imac`).
//!     - GCC distinguishes the ABI from the architecture, using its pre-existing `[i]lp` prefixes and a very restricted set of suffixes
//! 3. The standard defines no explicit set relationship between the `i` and `e` base instruction sets; this package makes the strong claim that `e` is a proper subset of `i`, so e.g. retaining the `e` instruction set from a `riscv32i` chip will produce a `riscv32e` target.
//!     - The instructions _do_ form a proper subset (every `e` instruction is a valid `i` instruction, but not vice versa).
//!     - The ABIs are defined to be compatible with each other TODO: calling into a `e` function from `i` works, but does calling into `i` from `e`?
//!
//! Additionally, the standard is fairly consistent in referring to "base" instruction sets vs. "extension", but for convenience and backwards compatibility this package largely allows referring to base instruction sets as "extensions."
//! # Usage in build.rs
//!
//! Most commonly used in `build.rs` to select from a set of pre-assembled objects for linking, i.e.:
//!
//! ```no_run
//! use std::{env, path::PathBuf, fs};
//! use riscv_target::Target;
//!
//! let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
//! let name = env::var("CARGO_PKG_NAME").unwrap();
//!
//! let target = "riscv32imac"; // usually via env::var("TARGET").unwrap();
//! let mut target = Target::from_target_str(&target);
//!
//! target.retain_extensions("ifc"); // <-- varies!
//!
//! let target = target.to_string();
//!
//! fs::copy(
//!   format!("bin/preassembled_{target}.a"),
//!   out_dir.join(format!("libriscv.a")),
//! );
//!
//! println!("cargo:rustc-link-lib=static={name}");
//! println!("cargo:rustc-link-search={}", out_dir.display());
//! ```
//!
//! This approach allows supporting more efficient binaries on platforms that support the necessary features, while still allowing graceful fallback for those that do not. For example, retaining the `i`, `f`, and `c` instruction sets from a descriptor like `riscv32iacv-...` will produce `riscv32ic-...`, allowing you to ignore the presence of unrelated instruction sets (here, `a` and `v`) while still taking advantage of compressed instructions.
//!
//! Note: this implies that you'll build supporting binaries for each possible subset of the above extensions (here, `i`, `ic`, `if`, `ifc`).
//!

#![deny(deprecated)]

use std::{
    collections::HashSet,
    convert::TryInto,
    fmt::{Debug, Display},
    hash::Hash,
    iter::FromIterator,
};
use std::{convert::TryFrom, str::FromStr};

// TODO: how to handle this?
// "The counters and timers are no longer considered mandatory parts of the standard base
// ISAs, and so the CSR instructions required to access them have been moved out of the base ISA
// chapter into this separate chapter."

// (and, like, revisions in general?)
// (i.e. when the rust targets were defined, `i` implied Zicsr; now it does not. Whuh oh!)

// TODO[all]: case insensitivity

// TODO how do you subset an enum's variants? Or, in general, take a generic (/ const) parameter for that?
//    like, if we had `Prefixable<{"ilp"}>` and `Prefixable<{"lp"}>` for GCC calling conventions, could we also say `PrefixableRestricted<{"ilp", {32}, { ["", "d", "f"] }>` or something for the `ilp32{,f,d}` subset?
//    and/or, would it be cooler to do `Prefixable<{"lp"}, {Base::RV64}, {}>

/// Represents a standard RISC-V ISA target triple
pub struct Target {
    #[deprecated(
        since = "0.2.0",
        note = "extensions are not a single character in width, use [`exts`] instead"
    )]
    pub extensions: HashSet<char>,
    // TODO: try to maintain this, or nah?
    #[deprecated(
        since = "0.2.0",
        note = "suffix is not part of the standard, nor would any supported rustc triples parse with one"
    )]
    pub suffix: String,
    #[deprecated(
        since = "0.2.0",
        note = "bit-width does not uniquely identify a base integer ISA, use [`base`] instead"
    )]
    pub bits: u32,
    #[deprecated(since = "0.2.0", note = "use `base` instead")]
    pub base_extension: char,

    pub base: Base,
    pub exts: Extensions,
    pub vendor_os: String,
}

// TODO:
// - [x] is there an alternative to From<T> that doesn't clone/copy/move?
//     - does it matter? if we want to .to_ascii_lowercase, that's a copy of the input anyway
//     - perhaps we do not do that? and canonicalize later?
//     - not really: AsRef doesn't apply, and we could do `From<&T>` or w/e but we need to own & be owned rn
// - [ ] enum Insts { I, E, M, etc. } ? and Extensions -> InstructionSet or something?
// - [ ] find and _eliminate_ `clone`s
// - [ ] remove .0 references to hash set for Extensions
// - [ ] probably, remove String errors :-/
// - [ ] is there a way to expose the ~same interface, but with different usage strategies:
//     - simple ownership vs. referential lifetimes ? (i.e. `String`s vs lots of `&str`s)
//     - versioned vs unversioned extensions? Since most of the time, versions are neither present nor desired?

#[derive(Debug, PartialEq, Eq)]
pub struct Extensions(HashSet<Extension>);

impl<S> From<S> for Extensions
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        let value = value.as_ref().to_ascii_lowercase();
        let mut chars = value.chars();
        let mut exts = Extensions(HashSet::new());

        while let Some(c) = chars.next() {
            match c {
                // TODO other implications (d => f, Zam => a)
                c if c == 'g' => {
                    for ext in "imafd".chars() {
                        exts.0.insert(ext.into());
                    }
                }

                'i' | 'e' => {
                    // back compat
                    // also, awkwardly: parsing
                    exts.0.insert(Extension {
                        name: ExtName::Std(c),
                        ..Default::default()
                    });
                }

                '_' => {} // discard

                'z' | 's' | 'h' | 'x' => {
                    let name: String = std::iter::once(c)
                        .chain(chars.by_ref())
                        .take_while(|&ch| ch != '_')
                        .collect();

                    let name = match c {
                        'z' if name.starts_with("zxm") => ExtName::StdM(name),
                        'z' => ExtName::StdZ(name),
                        's' => ExtName::StdS(name),
                        'h' => ExtName::StdH(name),
                        'x' => ExtName::NonStdX(name),
                        _ => unreachable!(),
                    };

                    exts.0.insert(Extension {
                        name,
                        ..Default::default()
                    });
                }

                c => {
                    exts.0.insert(Extension {
                        name: ExtName::Std(c),
                        version: None,
                    });
                }
            };
        }

        exts
    }
}

impl FromIterator<Extension> for Extensions {
    fn from_iter<T: IntoIterator<Item = Extension>>(iter: T) -> Self {
        Extensions(HashSet::from_iter(iter))
    }
}

impl Extensions {
    /// Remove and return base instruction sets ('i', 'e')
    fn remove_bases(&mut self) -> Vec<Extension> {
        let mut ret = vec![];
        self.0.retain(|ext| match ext.name {
            ExtName::Std('i') | ExtName::Std('e') => {
                ret.push(ext.clone());

                false
            }
            _ => true,
        });

        ret
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Base {
    RV32E,
    RV32I,

    RV64I,

    RV128I,
}

impl<W, C> TryFrom<(W, C)> for Base
where
    W: TryInto<u32> + Debug + Copy,
    <W as TryInto<u32>>::Error: Debug,
    C: Into<ExtName>,
{
    type Error = String;

    fn try_from(v: (W, C)) -> Result<Self, Self::Error> {
        use Base::*;
        let (w, c) = v;
        let w = w
            .try_into()
            .map_err(|e| format!("couldn't convert {w:?} to a u32: {e:?}"))?;
        match (w, c.into()) {
            (32, ExtName::Std('i')) => Ok(RV32I),
            (32, ExtName::Std('e')) => Ok(RV32E),

            (64, ExtName::Std('i')) => Ok(RV64I),

            (128, ExtName::Std('i')) => Ok(RV128I),

            (w @ 0..=31, _) | (w @ 33..=63, _) | (w @ 65..=127, _) | (w @ 129.., _) => Err(
                format!("unrecognized bit width (expected 32, 64, or 128): {w}"),
            ),

            (w, ExtName::Std(c @ 'e')) => Err(format!(
                "unrecognized base ISA for RV{w}: {c} (hint: 'e' is only defined for RV32)"
            )),
            (w, c) => Err(format!("unrecognized base ISA for RV{w}: {c:?}")),
        }
    }
}

impl Base {
    pub fn xlen<T: From<u8>>(&self) -> T {
        use Base::*;
        match self {
            RV32E | RV32I => 32.into(),

            RV64I => 64.into(),

            RV128I => 128.into(),
        }
    }

    // TODO: public ?
    // is there gonna be another base iset ? will it be a single char-name or not?
    fn as_char(&self) -> char {
        use Base::*;
        match self {
            RV32E => 'e',
            RV32I | RV64I | RV128I => 'i',
        }
    }
}

impl PartialEq<char> for Extension {
    fn eq(&self, other: &char) -> bool {
        match self.name {
            ExtName::Std(ref c) if c == other => true,
            _ => todo!(),
        }
    }
}

impl PartialEq<Extension> for char {
    fn eq(&self, other: &Extension) -> bool {
        other == self
    }
}

const ISET_ORDER: &str = "iemafdqlcbjtpvn";

#[derive(Debug)]
pub struct ParseError(ErrType, String);

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ParseError(err, ctx) = self;
        write!(f, "{}", err)?;
        if !ctx.is_empty() {
            write!(f, ": {}", ctx)?;
        }

        Ok(())
    }
}

pub enum ErrType {
    UnknownArchitecture,
    UnknownWidth,
    UnknownBase,
    ConflictingBases,
}

impl Debug for ErrType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownArchitecture => write!(f, "UnknownArchitecture (\"{}\")", self),
            Self::UnknownWidth => write!(f, "UnknownWidth (\"{}\")", self),
            Self::UnknownBase => write!(f, "UnknownBase (\"{}\")", self),
            Self::ConflictingBases => write!(f, "ConflictingBases (\"{}\")", self),
        }
    }
}

impl Display for ErrType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // concat
        use ErrType::*;
        match self {
            UnknownArchitecture => write!(f, "unknown target prefix, expected `riscv`"),
            UnknownWidth => write!(f, "unknown integer width, expected 32, 64, or 128"),
            UnknownBase => write!(f, "unknown integer base, expected one of: [32i, 32e, 64i, 128i] (explicitly, or implied by `g`)"),
            ConflictingBases => write!(f, "saw conflicting bases"),
        }
    }
}

impl FromStr for Target {
    type Err = ParseError;

    fn from_str(target_str: &str) -> Result<Self, Self::Err> {
        use ErrType::*;

        let str = target_str.to_ascii_lowercase();
        let (str, vendor_os) = str.split_once('-').unwrap_or((target_str, ""));
        let vendor_os = vendor_os.to_owned();

        // legacy field
        let suffix = str
            .find(|c| !matches!(c, 'a'..='z' | '0'..='9' | '_'))
            .unwrap_or(str.len());
        let (str, suffix) = str.split_at(suffix);
        let suffix = suffix.to_owned();

        let str = str
            .strip_prefix("riscv")
            .ok_or_else(|| ParseError(UnknownArchitecture, target_str.to_owned()))?;

        // 32imac -> (32, imac)
        let modules = str.find(|c: char| !c.is_ascii_digit()).unwrap_or(0);
        let (xlen, modules) = str.split_at(modules);

        let xlen: u32 = match xlen {
            "32" => Ok(32),
            "64" => Ok(64),
            "128" => Ok(128),

            _ => Err(ParseError(UnknownWidth, format!("{xlen} in {target_str}"))),
        }?;

        let mut exts = Extensions::from(modules);
        let bases = exts.remove_bases();
        let base = match &bases.as_slice() {
            &[] => Err(ParseError(UnknownBase, target_str.to_owned())),
            &[b] => Base::try_from((xlen, b.name.clone()))
                .map_err(|s| ParseError(UnknownBase, format!("{s} in {target_str}"))),
            [bases @ ..] => Err(ParseError(
                ConflictingBases,
                format!("{bases:?} in {target_str}"),
            )),
        }?;

        let target_flags = exts
            .0
            .iter()
            .filter_map(|e| match e.name {
                ExtName::Std(ch) => Some(ch),
                _ => None,
            })
            .collect();

        #[allow(deprecated)]
        Ok(Self {
            extensions: target_flags,

            bits: base.xlen(),
            base_extension: base.as_char(),

            suffix,

            base,
            exts,
            vendor_os,
        })
    }
}

impl Target {
    pub fn from_target_str(target_str: &str) -> Self {
        target_str.parse().expect("failed to parse target")
    }

    fn is_g_extension<E: Into<Extension>>(e: E) -> bool {
        match e.into().name {
            ExtName::Std('m') | ExtName::Std('a') | ExtName::Std('f') | ExtName::Std('d') => true,

            // todo case insensitivity
            ExtName::StdZ(ext) if ext == "Zicsr" => true,
            ExtName::StdZ(ext) if ext == "Zifencei" => true,

            _ => false,
        }
    }

    pub fn retain_extensions<E>(&mut self, extensions: E)
    where
        E: Into<Extensions>,
    {
        let extensions = extensions.into();
        let has_g = extensions.0.contains(&'g'.into());
        #[allow(deprecated)]
        {
            self.extensions.retain(|&e| {
                (has_g && Self::is_g_extension(e)) || extensions.0.contains(&e.into())
            });
        }

        self.exts.0.retain(|e| {
            has_g && Self::is_g_extension(e.clone()) || extensions.0.iter().any(|ext| e == ext)
        });
    }

    // TODO into extensions
    pub fn remove_extensions(&mut self, extensions: &str) {
        for e in extensions.chars() {
            match e {
                'e' | 'i' => {}
                'g' => self.remove_extensions("imafd"),
                e => {
                    #[allow(deprecated)]
                    {
                        self.extensions.remove(&e);
                    }
                    self.exts.0.remove(&e.into());
                }
            }
        }
    }

    // TODO into extensions
    pub fn add_extensions(&mut self, extensions: &str) {
        for e in extensions.to_lowercase().chars() {
            match e {
                'e' | 'i' => {}
                'g' => self.add_extensions("imafd"),
                e => {
                    #[allow(deprecated)]
                    {
                        self.extensions.insert(e);
                    }
                    self.exts.0.insert(e.into());
                }
            }
        }
    }

    pub fn has_extension<E>(&self, extension: E) -> bool
    where
        E: Into<Extension>,
    {
        use ExtName::*;
        match extension.into().name {
            Std(c) => match c.to_ascii_lowercase() {
                // backwards compatibility, TODO prefer using?
                'e' | 'i' => self.base.as_char() == c,
                'g' => {
                    // this is fine until we actually handle implications properly
                    #[allow(deprecated)]
                    {
                        self.base_extension == 'i'
                            && "mafd".chars().all(|e| self.extensions.contains(&e))
                    }
                }
                e => self.exts.0.contains(&e.into()),
            },
            _ => todo!(),
        }
    }
}

/// e.g. "a" (or "A", case insensitive), "Zicsr", "Zifencei2p0", "Svinval", "Xhwacha"
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExtName {
    // see also: Base
    Std(char),
    StdZ(String),
    StdS(String),
    StdH(String),
    StdM(String),
    NonStdX(String),
}

// impl FromIterator<char> for Result<ExtName, Err> {
//     fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
//         let mut iter = iter.into_iter();
//         match iter.next().expect("name must have at least one character") {
//             _ => {}
//         }
//     }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Extension {
    pub name: ExtName,
    pub version: Option<Version>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Version {}

impl Default for Extension {
    fn default() -> Self {
        Self {
            name: ExtName::Std('i'),
            version: Default::default(),
        }
    }
}

impl From<char> for Extension {
    fn from(c: char) -> Self {
        Extension {
            name: ExtName::Std(c),
            ..Default::default()
        }
    }
}

impl ToString for Target {
    fn to_string(&self) -> String {
        let has_g = self.has_extension('g');

        let xlen: u8 = self.base.xlen();
        let base = if has_g { 'g' } else { self.base.as_char() };
        // TODO: remove clone, cloned?
        let mut target_exts: HashSet<_> = self
            .exts
            .0
            .iter()
            .filter(|&e| !has_g || !Self::is_g_extension(e.clone()))
            .cloned()
            .collect();

        let mut exts = String::new();
        for e in ISET_ORDER.chars() {
            if target_exts.remove(&e.into()) {
                exts.push(e)
            }
        }

        // target_exts.part
        let mut bs = false;

        {
            let mut yey = vec![];
            target_exts.retain(|e| match &e.name {
                ExtName::StdZ(zext) => {
                    yey.push(zext.clone());

                    false
                }
                _ => true,
            });

            for e in ISET_ORDER.chars() {
                let mut yey2 = vec![];

                yey.retain(|yy| {
                    if yy.starts_with(&format!("z{e}")) {
                        yey2.push(yy.clone());
                        false
                    } else {
                        true
                    }
                });

                yey2.sort();

                for zext in yey2 {
                    if bs {
                        exts.push('_');
                    }
                    bs = true;
                    exts.push('Z');
                    exts.push_str(&zext[1..]);
                }
            }
        }

        {
            let mut yey = vec![];
            target_exts.retain(|e| match &e.name {
                ExtName::StdS(sext) => {
                    yey.push(sext.clone());

                    false
                }
                _ => true,
            });

            yey.sort();

            for sext in yey {
                if bs {
                    exts.push('_');
                }
                bs = true;
                exts.push('S');
                exts.push_str(&sext[1..]);
            }
        }

        {
            let mut yey = vec![];
            target_exts.retain(|e| match &e.name {
                ExtName::StdH(hext) => {
                    yey.push(hext.clone());

                    false
                }
                _ => true,
            });

            yey.sort();

            for sext in yey {
                if bs {
                    exts.push('_');
                }
                bs = true;
                exts.push('H');
                exts.push_str(&sext[1..]);
            }
        }

        {
            let mut yey = vec![];
            target_exts.retain(|e| match &e.name {
                ExtName::StdM(mext) => {
                    yey.push(mext.clone());

                    false
                }
                _ => true,
            });

            yey.sort();

            for mext in yey {
                if bs {
                    exts.push('_');
                }
                bs = true;
                exts.push('Z');
                exts.push_str(&mext[1..]);
            }
        }

        {
            let mut yey = vec![];
            target_exts.retain(|e| match &e.name {
                ExtName::NonStdX(xext) => {
                    yey.push(xext.clone());

                    false
                }
                _ => true,
            });

            yey.sort();

            for xext in yey {
                if bs {
                    exts.push('_');
                }
                bs = true;
                exts.push('X');
                exts.push_str(&xext[1..]);
            }
        }

        if !target_exts.is_empty() {
            exts.push('_');

            let mut unknown = target_exts
                .into_iter()
                .filter_map(|e| match e.name {
                    ExtName::Std(c) => Some(c),
                    _ => todo!(),
                })
                .collect::<Vec<_>>();

            unknown.sort();

            exts.push_str(&unknown.iter().collect::<String>());
        }

        let vendor_os = &self.vendor_os;

        format!("riscv{xlen}{base}{exts}-{vendor_os}")
    }
}

#[cfg(test)]
mod tests {
    extern crate test_case;

    use std::str::FromStr;

    use crate::{Extension, Extensions};

    use self::test_case::test_case;
    use super::Base;
    use super::Target;

    #[test]
    fn simplest_case() {
        let target = Target::from_target_str("riscv32ima-unknown-none-elf");
        #[allow(deprecated)]
        {
            assert_eq!(target.bits, 32);
            assert_eq!(target.base_extension, 'i');
            assert_eq!(target.extensions, "ma".chars().collect());
            assert_eq!(target.suffix, "");
        }
        assert_eq!(target.base, Base::RV32I);
        // TODO surely there's another way
        assert_eq!(
            target.exts,
            <Extensions as std::iter::FromIterator<Extension>>::from_iter({
                use crate::ExtName::Std;
                [
                    Extension {
                        name: Std('m'),
                        version: None,
                    },
                    Extension {
                        name: Std('a'),
                        version: None,
                    },
                ]
            })
        );
        assert_eq!(target.vendor_os, "unknown-none-elf");

        assert_eq!(target.to_string(), "riscv32ima-unknown-none-elf");
    }

    #[test]
    fn multiple_bases() {
        use crate::{ErrType::ConflictingBases, ParseError};
        let res = Target::from_str("riscv32ie");

        assert!(matches!(res, Err(ParseError(ConflictingBases, ..))));

        // descriptive, not normative
        let res = Target::from_str("riscv32ii");
        assert!(matches!(
            res,
            Ok(Target {
                base: Base::RV32I,
                ..
            })
        ))
    }

    /// see https://f004.backblazeb2.com/file/shared-sethp/riscv-spec-20191213-2.pdf#section.27.11
    #[test_case("riscv32ami", Base::RV32I, "ima" ; "common 32-bit")]
    #[test_case("riscv64ami", Base::RV64I, "ima" ; "common 64-bit")]
    #[test_case("riscv128ami", Base::RV128I, "ima" ; "common 128-bit")]
    #[test_case("riscv32cme", Base::RV32E, "emc" ; "embedded")]
    #[test_case("riscv32Zifencei_acm_i", Base::RV32I, "imacZifencei" ; "with Z extension")]
    #[test_case("riscv32iZifencei_aZicsr_cm", Base::RV32I, "imacZicsr_Zifencei" ; "multiple Zi* extensions")]
    #[test_case("riscv32iZicsr_Zifencei_Zam_Ztso", Base::RV32I, "iZicsr_Zifencei_Zam_Ztso" ; "multiple Z* extensions")]
    #[test_case("riscv32iSvpbmt_c", Base::RV32I, "icSvpbmt" ; "with S extension")]
    // currently, no standard H extensions have been ratified
    #[test_case("riscv32iHdef_c", Base::RV32I, "icHdef" ; "with H extension")]
    // currently, no standard machine extensions have been ratified
    #[test_case("riscv32iZxmjkl_c", Base::RV32I, "icZxmjkl" ; "with Machine-level extension")]
    #[test_case("riscv32iafdqlcbjtpvnZicsr_Zifencei_Zam_Ztso_Sdef_Hghi_Zxmjkl_Xmno", Base::RV32I,
                       "iafdqlcbjtpvnZicsr_Zifencei_Zam_Ztso_Sdef_Hghi_Zxmjkl_Xmno"
                ; "with all defined extension types"
    )]
    #[test_case("riscv32i_koruwy", Base::RV32I, "i_koruwy" ; "unknown extensions")]
    fn order_is_canonicalized(isa: &str, base: Base, want: &str) {
        let target = Target::from_target_str(&format!("{isa}-unknown-none-elf"));
        let xlen = base.xlen();
        #[allow(deprecated)]
        {
            assert_eq!(target.bits, xlen);
            assert_eq!(target.base_extension, base.as_char());
            assert_eq!(target.suffix, "");
        }
        assert_eq!(target.base, base);
        assert_eq!(target.vendor_os, "unknown-none-elf");

        assert_eq!(
            target.to_string(),
            format!("riscv{xlen}{want}-unknown-none-elf")
        );
    }

    #[test]
    fn general_purpose_extensions_are_expanded() {
        let target = Target::from_target_str("riscv32gc-unknown-none-elf");
        #[allow(deprecated)]
        {
            assert_eq!(target.bits, 32);
            assert_eq!(target.base_extension, 'i');
            assert_eq!(target.extensions, "mafdc".chars().collect());
            assert_eq!(target.suffix, "");
        }
        assert_eq!(target.base, Base::RV32I);
        assert_eq!(target.vendor_os, "unknown-none-elf");

        assert_eq!(target.to_string(), "riscv32gc-unknown-none-elf");
    }

    #[test_case("riscv32imac", "c", "riscv32ic" ; "present extension")]
    #[test_case("riscv32imac", "fd", "riscv32i" ; "missing extensions")]
    #[test_case("riscv32imac", "cfd", "riscv32ic" ; "both missing and present")]
    #[test_case("riscv32imac", "mac", "riscv32imac" ; "canonical order")]
    #[test_case("riscv32imac", "cma", "riscv32imac" ; "non-canonical order")]
    #[test_case("riscv32imac", "i", "riscv32i" ; "retain base i")]
    #[test_case("riscv32e", "e", "riscv32e" ; "retain base e")]
    #[test_case("riscv32e", "i", "riscv32e" ; "retain base doesn't upgrade")]
    #[test_case("riscv32i", "e", "riscv32i" ; "retain base doesn't downgrade")]
    #[test_case("riscv32imacj", "g", "riscv32ima" ; "retain extension g")]
    #[test_case("riscv32iZicsr_Zifencei", "Zicsr_Zifencei", "riscv32iZicsr_Zifencei" ; "retain explicit Z* extensions")]
    // TODO: implication
    // #[test_case("riscv32gc", "Zicsr_Zifencei", "riscv32iZicsr_Zifencei" ; "retain Z* extensions")]
    fn retain_extensions(isa: &str, retain: &str, want: &str) {
        let mut target = Target::from_target_str(&format!("{isa}-unknown-none-elf"));
        target.retain_extensions(retain);

        assert_eq!(target.to_string(), format!("{want}-unknown-none-elf"));
    }

    /// examples collected from the wild
    /// target lists taken from `rustc --print target-list | grep riscv | grep unknown-none-elf`
    #[test]
    fn retain_extensions_from_the_wild() {
        for (riscv_isa, want) in [
            // 32-bit
            ("riscv32i", "riscv32i"),
            ("riscv32im", "riscv32im"),
            ("riscv32imac", "riscv32imc"),
            ("riscv32imc", "riscv32imc"),
            // 64-bit
            ("riscv64gc", "riscv64imfdc"),
            ("riscv64imac", "riscv64imc"),
        ] {
            let rustc_target = format!("{riscv_isa}-unknown-none-elf");
            let want = format!("{want}-unknown-none-elf");
            let target = rustc_target.to_owned(); // simulate std::env lookup

            // https://github.com/rust-embedded/riscv-rt/blob/e95dc95a85a50277340ca67459f7e41d61b49ceb/build.rs#L16
            let got = {
                let mut target = Target::from_target_str(&target);
                target.retain_extensions("imfdc");

                target.to_string()
            };

            assert_eq!(
                got, want,
                "from {rustc_target:?}.retain_extensions(\"imfdc\")"
            );
        }

        for (riscv_isa, want) in [
            // 32-bit
            ("riscv32i", "riscv32i"),
            ("riscv32im", "riscv32i"),
            ("riscv32imac", "riscv32i"),
            ("riscv32imc", "riscv32i"),
            // 64-bit
            ("riscv64gc", "riscv64if"),
            ("riscv64imac", "riscv64i"),
        ] {
            let rustc_target = format!("{riscv_isa}-unknown-none-elf");
            let want = format!("{want}-unknown-none-elf");
            let target = rustc_target.to_owned(); // simulate std::env lookup

            // https://github.com/9names/bl702-hal/blob/416c6b87021df3d7750f8c17cda32dc4397412b5/build.rs#L15-L18
            let got = {
                let mut target = Target::from_target_str(&target);
                target.retain_extensions("if");

                target.to_string()
            };

            assert_eq!(got, want, "from {rustc_target:?}.retain_extensions(\"if\")");
        }

        for (riscv_isa, want) in [
            // 32-bit
            ("riscv32i", "riscv32i"),
            ("riscv32im", "riscv32i"),
            ("riscv32imac", "riscv32ic"),
            ("riscv32imc", "riscv32ic"),
            // 64-bit
            ("riscv64gc", "riscv64ic"),
            ("riscv64imac", "riscv64ic"),
        ] {
            let rustc_target = format!("{riscv_isa}-unknown-none-elf");
            let want = format!("{want}-unknown-none-elf");
            let target = rustc_target.to_owned(); // simulate std::env lookup

            // https://github.com/LearningOS/rust-based-os-comp2023/blob/717259bb74e0952bba4be1b1b7f91e0948bc99fa/ci-user/riscv/build.rs#L14
            let got = {
                let mut target = Target::from_target_str(&target);
                target.retain_extensions("ic");

                target.to_string()
            };

            assert_eq!(
                got, want,
                "from {rustc_target:?}.retain_extensions(\"ic\") "
            );
        }
    }

    #[test]
    fn remove_missing_extensions() {
        let mut target = Target::from_target_str("riscv32imac-unknown-none-elf");
        target.remove_extensions("fd");

        assert_eq!(target.to_string(), "riscv32imac-unknown-none-elf");
    }

    // these make the strong claim that the e abi is both upwards and downwards compatible with the i abi
    mod dubious {
        use crate::Target;

        #[ignore = "confirm i/e substitutability"]
        #[test]
        fn remove_base_extension() {
            let mut target = Target::from_target_str("riscv32imac-unknown-none-elf");
            target.remove_extensions("i");

            assert_eq!(target.to_string(), "riscv32emac-unknown-none-elf");
        }

        #[ignore = "confirm i/e substitutability"]
        #[test]
        fn remove_base_extension_downgrade() {
            let mut target = Target::from_target_str("riscv32imac-unknown-none-elf");
            target.remove_extensions("e");

            assert_eq!(target.to_string(), "riscv32imac-unknown-none-elf");
        }

        #[ignore = "confirm i/e substitutability"]
        #[test]
        fn remove_base_extension_e() {
            let mut target = Target::from_target_str("riscv32emac-unknown-none-elf");
            target.remove_extensions("e");

            assert_eq!(target.to_string(), "riscv32emac-unknown-none-elf");
        }

        #[ignore = "confirm i/e substitutability"]
        #[test]
        fn remove_extension_g() {
            let mut target = Target::from_target_str("riscv32emacj-unknown-none-elf");
            target.remove_extensions("g");

            assert_eq!(target.to_string(), "riscv32ecj-unknown-none-elf");
        }

        #[ignore = "confirm i/e substitutability"]
        #[test]
        fn add_base_extension_i_upgrades() {
            let mut target = Target::from_target_str("riscv32emac-unknown-none-elf");
            target.add_extensions("i");

            assert_eq!(target.to_string(), "riscv32imac-unknown-none-elf");
        }
    }

    #[test]
    fn add_base_extension_e() {
        let mut target = Target::from_target_str("riscv32imac-unknown-none-elf");
        target.add_extensions("e");

        assert_eq!(target.to_string(), "riscv32imac-unknown-none-elf");
    }

    #[test]
    fn suffix() {
        let target = Target::from_target_str("riscv32imac*-unknown-none-elf");

        assert_eq!(target.base, Base::RV32I);
        #[allow(deprecated)]
        {
            assert_eq!(target.suffix, "*");
        }
        assert_eq!(target.vendor_os, "unknown-none-elf");
    }

    #[test]
    fn add_missing_extensions() {
        let mut target = Target::from_target_str("riscv32emac-unknown-none-elf");
        target.add_extensions("fd");

        assert_eq!(target.to_string(), "riscv32emafdc-unknown-none-elf");
    }

    #[test]
    fn add_present_extensions() {
        let mut target = Target::from_target_str("riscv32emac-unknown-none-elf");
        target.add_extensions("ma");

        assert_eq!(target.to_string(), "riscv32emac-unknown-none-elf");
    }

    #[ignore = "dubious?"]
    #[test]
    fn add_extension_g() {
        let mut target = Target::from_target_str("riscv32emac-unknown-none-elf");
        target.add_extensions("g");

        assert_eq!(target.to_string(), "riscv32gc-unknown-none-elf");
    }

    #[ignore = "dubious?"]
    #[test]
    fn has_base_extension_i() {
        let target = Target::from_target_str("riscv32imac-unknown-none-elf");

        assert!(target.has_extension('i'));
        assert!(target.has_extension('e'));
    }

    #[test]
    fn has_base_extension_e() {
        let target = Target::from_target_str("riscv32emac-unknown-none-elf");

        assert!(!target.has_extension('i'));
        assert!(target.has_extension('e'));
    }

    #[test]
    fn has_extension_if_present() {
        let target = Target::from_target_str("riscv32imac-unknown-none-elf");

        assert!(target.has_extension('c'));
    }

    #[test]
    fn has_extension_if_missing() {
        let target = Target::from_target_str("riscv32imac-unknown-none-elf");

        assert!(!target.has_extension('f'));
    }

    #[test]
    fn has_extension_g_if_missing() {
        let target = Target::from_target_str("riscv32imac-unknown-none-elf");

        assert!(!target.has_extension('g'));
    }

    #[test]
    fn has_extension_g_if_present() {
        let target = Target::from_target_str("riscv32imafd-unknown-none-elf");

        assert!(target.has_extension('g'));
    }

    // TODO: more implication tests, including making sure g == expanded set of g
    // TODO: versions (how to handle suffix?)
}
