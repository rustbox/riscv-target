//! experiment2: associated type shenanigans

pub use self::ver2017::Target as Target2;
use std::{cmp::Ordering, convert::TryFrom, fmt::Debug, str::FromStr};

pub struct Target<Spec>(Vec<Spec::ISet>)
where
    Spec: self::Spec;

impl<Spec> Target<Spec>
where
    Spec: self::Spec,
{
    // well, this is forced to exist because rustc can't apparently use a type alias as a constructor? cool.
    // e.g. Target::new(...) is fine, but Target(...) is `can't use a type alias as a constructor`
    pub fn new(isns: Vec<Spec::ISet>) -> Self {
        Self(isns)
    }

    pub fn from_target_str(s: &str) -> Self {
        s.parse().expect("failed to parse target")
    }
}

impl<Spec> FromStr for Target<Spec>
where
    Spec: self::Spec,
{
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use self::PartialError::*;

        let s = s.strip_prefix("riscv32").unwrap_or(s);

        let mut chars = s.chars();
        let mut ret = vec![];

        while let Some(ch) = chars.next() {
            match ch {
                '_' => {} // discard

                // TODO implications?
                // ch if ch.implies_stuff() => {}
                ch => match Spec::ISet::try_from(ch) {
                    Ok(iset) => ret.push(iset),
                    Err(Failure(err)) => return Err(err.into()),
                    Err(NeedsMore) => {
                        let name: String = std::iter::once(ch)
                            .chain(chars.by_ref())
                            .take_while(|&ch| ch != '_')
                            .collect();

                        // TODO: is there a way to avoid the map_err? IOW, how can I say "because their error is Into our error, then just use that for the From<our error>"?
                        let iset = Spec::ISet::try_from(name.as_str()).map_err(Into::into)?;
                        ret.push(iset)
                    }
                },
            }
        }

        Ok(Self(ret))
    }
}

impl<Spec> ToString for Target<Spec>
where
    Spec: self::Spec,
{
    fn to_string(&self) -> String {
        let Target(isets) = self;
        let mut ret = String::from("riscv32");
        let mut needs_underscore_bools_are_bs = false;
        // hmm, it might be nice to intersect first, somehow? since this requires writing all of the impls to get any to work
        for ch in Spec::ORDER.chars() {
            match Spec::ISet::try_from(ch) {
                Ok(iset) => {
                    if isets.contains(&iset) {
                        ret.push(ch)
                    }
                }

                Err(PartialError::NeedsMore) => {
                    // uhhh....
                    let mut stuff: Vec<_> = isets.iter().filter(|iset| iset.zzz(ch)).collect();

                    stuff.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Greater));

                    for iset in stuff {
                        if needs_underscore_bools_are_bs {
                            ret.push('_')
                        }
                        needs_underscore_bools_are_bs = true;
                        ret.push_str(iset.as_ref());
                    }
                }

                Err(err) => unreachable!(
                    "{} (from {}::ORDER) ought to have parsed: saw {:?}",
                    ch,
                    std::any::type_name::<Spec>(),
                    err
                ),
            }
        }
        ret
    }
}

#[derive(Debug)]
pub enum PartialError<T>
where
    T: Debug,
{
    Failure(T),
    NeedsMore,
}

pub trait Spec: Sized {
    const ORDER: &'static str;

    type ParseError: Into<<Target<Self> as FromStr>::Err> + Debug;
    type ISet: self::ISet
        + TryFrom<char, Error = PartialError<Self::ParseError>>
        + for<'a> TryFrom<&'a str, Error = Self::ParseError>;

    fn partial_cmp(a: char, b: char) -> Option<Ordering> {
        // ugh, this is O(n^3) when it's called from inside of the sort from inside the
        Self::ORDER.find(a).and_then(|a_idx| {
            Self::ORDER
                .find(b)
                .and_then(|b_idx| a_idx.partial_cmp(&b_idx))
        })
    }
}

pub trait ISet
where
    Self: PartialEq + PartialOrd + AsRef<str>,
{
    fn zzz(&self, ch: char) -> bool;
}

pub mod ver2017 {
    use std::convert::TryFrom;

    use super::PartialError;

    #[derive(PartialEq)]
    pub enum ISet {
        I,
        M,
        A,
        C,
        // TODO ...

        // TODO: String still sucks
        X(String),
        S(String),
        SX(String),
    }

    impl TryFrom<char> for ISet {
        type Error = PartialError<String>;

        fn try_from(ch: char) -> Result<Self, Self::Error> {
            match ch {
                'i' | 'I' => Ok(Self::I),
                'm' | 'M' => Ok(Self::M),
                'a' | 'A' => Ok(Self::A),
                'c' | 'C' => Ok(Self::C),
                // TODO ...
                'x' | 'X' | 's' | 'S' => Err(PartialError::NeedsMore),

                _ => Err(PartialError::Failure(format!("dunno about {ch}"))),
            }
        }
    }

    impl TryFrom<&str> for ISet {
        type Error = String;

        fn try_from(value: &str) -> Result<Self, Self::Error> {
            let mut chars = value.chars();
            if let Some(ch) = chars.next() {
                match ch {
                    'x' | 'X' => Ok(Self::X(value.to_owned())),
                    's' | 'S' => match chars.next() {
                        Some('x') | Some('X') => Ok(Self::SX(value.to_owned())),

                        _ => Ok(Self::S(value.to_owned())),
                    },

                    _ => todo!(),
                }
            } else {
                Err(format!("vas ist {value:?} ?"))
            }
        }
    }

    impl AsRef<str> for ISet {
        fn as_ref(&self) -> &str {
            match self {
                Self::I => "i",
                Self::M => "m",
                Self::A => "a",
                Self::C => "c",

                Self::X(s) | Self::S(s) | Self::SX(s) => s,
            }
        }
    }

    impl PartialOrd for ISet {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            match (self, other) {
                (a, b) if a == b => Some(std::cmp::Ordering::Equal),

                (Self::S(a), Self::S(b)) => {
                    match (a.chars().nth(1), b.chars().nth(1)) {
                        (Some(ac), Some(bc)) if ac == bc => a.partial_cmp(b),
                        (Some(a), Some(b)) => <Spec as super::Spec>::partial_cmp(a, b),

                        (Some(_), None) => Some(std::cmp::Ordering::Greater), // Sxxx vs S
                        (None, Some(_)) => Some(std::cmp::Ordering::Less),

                        (None, None) => unreachable!(), // S == S
                    }
                }

                (Self::SX(_), Self::S(_)) => Some(std::cmp::Ordering::Greater),
                (Self::S(_), Self::SX(_)) => Some(std::cmp::Ordering::Less),

                (Self::SX(a), Self::SX(b)) => a.partial_cmp(b),
                (Self::X(a), Self::X(b)) => a.partial_cmp(b),

                _ => None,
            }
        }
    }

    impl super::ISet for ISet {
        fn zzz(&self, ch: char) -> bool {
            match (self, ch.to_ascii_lowercase()) {
                (Self::I, 'i') => true,
                (Self::M, 'm') => true,
                (Self::A, 'a') => true,
                (Self::C, 'c') => true,
                // TODO ...
                (Self::X(_), 'x') => true,
                (Self::S(_), 's') => true,
                (Self::SX(_), 's') => true,

                _ => false,
            }
        }
    }

    pub struct Spec;

    impl super::Spec for Spec {
        const ORDER: &'static str = "imacXS"; // NB: x is before s, here

        // TODO
        // const ORDER: &'static str = "imafdgqlcbjtpvnXS"; // NB: x is before s, here

        type ParseError = String;
        type ISet = ISet;
    }

    pub type Target = super::Target<Spec>;

    #[cfg(test)]
    mod test {
        use super::Target;

        #[test]
        fn simple() {
            let target = Target::from_target_str("riscv32ic");

            assert_eq!(target.to_string(), "riscv32ic");
        }

        #[test]
        fn multichar() {
            let target = Target::from_target_str("riscv32icXmyext");

            assert_eq!(target.to_string(), "riscv32icXmyext");
        }

        #[test]
        fn multichar_sorted() {
            let target = Target::from_target_str("riscv32icXmyext_Xmno");

            assert_eq!(target.to_string(), "riscv32icXmno_Xmyext");
        }

        #[test]
        fn all_together_now() {
            let target =
                Target::from_target_str("riscv32icSXljk_Xmyext_Xmno_Sidef_Sajunk_SXtension");

            assert_eq!(
                target.to_string(),
                "riscv32icXmno_Xmyext_Sidef_Sajunk_SXljk_SXtension"
            );
        }

        #[test]
        fn whats_it_like_to_work_with() {
            let target = {
                use super::ISet::*;
                Target::new(vec![I, M, A, C, X("myext".to_owned())])
            };

            assert_eq!(
                target.to_string(),
                "riscv32icXmno_Xmyext_Sidef_Sajunk_SXljk_SXtension"
            );
        }
    }
}

pub mod ver2019 {}
