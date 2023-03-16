//! experiment1: traits with mostly-empty structs (i.e. `struct I`, `struct X(string)`)

#![allow(clippy::type_complexity)]

use std::{borrow::Borrow, str::FromStr};

pub struct Target1(
    Vec<&'static dyn Fn(char) -> Result<Box<dyn ISet>, String>>,
    Vec<Box<dyn ISet>>,
);

impl Target1 {
    pub fn from_target_str(s: &str) -> Self {
        s.parse().expect("failed to parse target")
    }
}

impl FromStr for Target1 {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let types: Vec<&'static dyn Fn(char) -> Result<Box<dyn ISet>, String>> =
            vec![&I::not_try_from, &C::not_try_from]; // TODO pass this in somehow?
        let mut parsed = vec![];

        let s = s.strip_prefix("riscv32").unwrap_or(s);

        for ch in s.chars() {
            for ty in types.iter() {
                if let Ok(s) = ty(ch) {
                    parsed.push(s);
                }
                // TODO: if none match?
            }
        }

        Ok(Self(types, parsed))
    }
}

impl ToString for Target1 {
    fn to_string(&self) -> String {
        let Target1(types, isets) = self;

        let mut ret = String::from("riscv32");
        // TODO: get this ordering directly from `types`, somehow?
        // we'd need something like a `::new` for each item to use for `not_not_eq`
        for ch in "imac".chars() {
            let mut cur: Option<Box<dyn ISet>> = None;
            for ref ty in types {
                if let Ok(i) = ty(ch) {
                    cur = Some(i);
                    break;
                }
            }
            if let Some(cur) = cur {
                for iset in isets {
                    if iset.not_not_eq(cur.borrow()) {
                        ret.push(ch);
                        break;
                    }
                }
            }
        }

        ret
    }
}

// I don't know how to make this nicer; trying to bound ourselves by PartialEq and TryFrom makes us not-object-safe?
// maybe we had to be Sized? I'm not sure I tried those with that bound
pub trait ISet {
    fn not_try_from(ch: char) -> Result<Box<dyn ISet>, String>
    where
        Self: Sized;

    fn not_not_eq(&self, other: &dyn ISet) -> bool {
        self.as_char() == other.as_char()
    }

    fn as_char(&self) -> char;
}

struct I;
struct C;

impl I {
    const CH: char = 'i';
}

impl ISet for I {
    fn not_try_from(ch: char) -> Result<Box<dyn ISet>, String>
    where
        Self: Sized,
    {
        if ch == Self::CH {
            Ok(Box::new(Self))
        } else {
            Err(format!("no match: {ch} != {}", Self::CH))
        }
    }

    fn as_char(&self) -> char {
        Self::CH
    }
}
impl ISet for C {
    fn not_try_from(ch: char) -> Result<Box<dyn ISet>, String>
    where
        Self: Sized,
    {
        if ch == 'c' {
            Ok(Box::new(Self))
        } else {
            Err(format!("no match: {ch} != c"))
        }
    }

    fn as_char(&self) -> char {
        'c'
    }
}

#[cfg(test)]
mod test {
    use super::Target1 as Target;

    #[test]
    fn simple() {
        let target = Target::from_target_str("riscv32ic");

        assert_eq!(target.to_string(), "riscv32ic");
    }
}
