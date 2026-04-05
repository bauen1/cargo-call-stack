use core::fmt;

use anyhow::anyhow;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while1},
    character::complete::{char, digit1, line_ending, not_line_ending, space1},
    combinator::{map, map_res, opt},
    error::ErrorKind,
    error_position,
    multi::{many0, many1, separated_list0},
    sequence::delimited,
    IResult,
};

mod define;
mod item;
mod ty;

use crate::ir::ty::type_;
pub use crate::ir::{define::Stmt, item::Item, ty::Type};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FnSig<'a> {
    pub inputs: Vec<Type<'a>>,
    pub output: Option<Box<Type<'a>>>,
}

impl<'a> FnSig<'a> {
    pub fn loosely_equal(&self, other: &Self) -> bool {
        self.inputs.len() == other.inputs.len()
            && self
                .inputs
                .iter()
                .zip(&other.inputs)
                .all(|(lhs, rhs)| lhs.loosely_equal(&rhs))
            && match (&self.output, &other.output) {
                (None, None) => true,
                (Some(lhs), Some(rhs)) => lhs.loosely_equal(&rhs),
                _ => false,
            }
    }
}

impl<'a> fmt::Display for FnSig<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(output) = &self.output {
            write!(f, "{}", output)?;
        } else {
            f.write_str("void")?;
        }

        f.write_str(" (")?;
        let mut is_first = true;
        for input in &self.inputs {
            if is_first {
                is_first = false;
            } else {
                f.write_str(", ")?;
            }

            write!(f, "{}", input)?;
        }
        f.write_str(")")
    }
}

pub fn parse(ll: &str) -> anyhow::Result<Vec<Item>> {
    items(ll).map(|t| t.1).map_err(|e| {
        let e = e.map(|e| {
            let offset = ll.len()-e.input.len();
            let mut cur = offset;
            for (n, line) in ll.split_inclusive('\n').enumerate() {
                match cur.checked_sub(line.len()) {
                    Some(it) => cur = it,
                    None => return format!("{:?} in line {}", e.code, n + 1),
                }
            }

            unreachable!("couldn't find line the parse error at offset {} refers to", offset)
        });
        anyhow!(
            "BUG: failed to parse LLVM IR; please submit a cargo-call-stack bug report and attach the `.ll` file: {:?}",
            e
        )
    })
}

fn items(i: &str) -> IResult<&str, Vec<Item>> {
    let mut items = Vec::new();
    let mut i = i;
    while !i.is_empty() {
        let (next_i, _) = many0(alt((line_ending, space1)))(i)?;
        i = next_i;
        if i.is_empty() {
            break;
        }

        match crate::ir::item::item(i) {
            Ok((next_i, item)) => {
                items.push(item);
                i = next_i;
            }
            Err(_) => {
                let (next_i, _) = not_line_ending(i)?;
                let (next_i, _) = opt(line_ending)(next_i)?;
                i = next_i;
            }
        }
    }
    Ok(("", items))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Comment;

fn comment(i: &str) -> IResult<&str, Comment> {
    let i = char(';')(i)?.0;
    let i = not_line_ending(i)?.0;
    Ok((i, Comment))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Ident<'a>(&'a str);

// LLVM LangRef: `[-a-zA-Z$._][-a-zA-Z$._0-9]*`
fn ident(i: &str) -> IResult<&str, Ident> {
    map_res(
        take_while1(|c: char| c.is_alphanumeric() || "-$._".contains(c)),
        |s: &str| {
            if s.chars().next().unwrap_or('\0').is_digit(10) {
                Err(())
            } else {
                Ok(Ident(s))
            }
        },
    )(i)
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Global<'a>(Option<&'a str>);

fn global(i: &str) -> IResult<&str, Global> {
    let i = char('@')(i)?.0;
    let (i, s) = alt((
        map(string, |s| Some(s.0)),
        map(digit1, |_| None),
        map(ident, |i| Some(i.0)),
    ))(i)?;
    Ok((i, Global(s)))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Local;

fn local(i: &str) -> IResult<&str, Local> {
    let i = char('%')(i)?.0;
    let i = alt((map(digit1, drop), map(ident, drop)))(i)?.0;
    Ok((i, Local))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Null;

fn null(i: &str) -> IResult<&str, Null> {
    let i = tag("null")(i)?.0;
    Ok((i, Null))
}

fn undef(i: &str) -> IResult<&str, Null> {
    let i = tag("undef")(i)?.0;
    Ok((i, Null))
}

// `internal`, `fastcc`, `dereferenceable(4)`, etc.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Attribute;

fn attribute(i: &str) -> IResult<&str, Attribute> {
    let (i, attr) = take_while1(|c: char| c.is_alphanumeric() || "_.".contains(c))(i)?;

    match attr {
        "double" | "float" | "void" | "ptr" | "bitcast" | "getelementptr" | "alias" | "global" | "constant" => {
            return Err(nom::Err::Error(error_position!(i, ErrorKind::Switch)));
        }
        _ => {}
    }

    let (i, opening) = opt(char('('))(i)?;
    let i = if opening.is_some() {
        let mut depth = 1;
        let mut pos = 0;
        let bytes = i.as_bytes();
        while depth > 0 && pos < bytes.len() {
            if bytes[pos] == b'(' {
                depth += 1;
            } else if bytes[pos] == b')' {
                depth -= 1;
            }
            pos += 1;
        }
        &i[pos..]
    } else if attr == "align" {
        let i = space1(i)?.0;
        digit1(i)?.0
    } else {
        i
    };

    Ok((i, Attribute))
}

// NOTE constant operation
#[derive(Clone, Copy, Debug, PartialEq)]
struct Bitcast<'a>(Option<&'a str>);

fn bitcast(i: &str) -> IResult<&str, Bitcast> {
    let i = tag("bitcast")(i)?.0;
    let i = space1(i)?.0;
    delimited(
        char('('),
        |i| {
            let i = type_(i)?.0;
            let i = space1(i)?.0;
            let (i, name) = alt((
                map(global, |g| g.0),
                // TODO(?) on this branch we should return the indices because we could be dealing
                // with a (statically allocated) struct that contains several function pointers
                map(getelementptr, |gep| gep.0),
            ))(i)?;
            let i = space1(i)?.0;
            let i = tag("to")(i)?.0;
            let i = space1(i)?.0;
            let i = type_(i)?.0;
            Ok((i, Bitcast(name)))
        },
        char(')'),
    )(i)
}

// NOTE constant operation
#[derive(Clone, Copy, Debug, PartialEq)]
struct GetElementPtr<'a>(Option<&'a str>);

fn getelementptr(i: &str) -> IResult<&str, GetElementPtr> {
    let i = tag("getelementptr")(i)?.0;
    let i = space1(i)?.0;
    let i = opt(|i| {
        let i = tag("inbounds")(i)?.0;
        space1(i)
    })(i)?
    .0;
    let (i, name) = delimited(
        char('('),
        |i| {
            let i = type_(i)?.0;
            let i = char(',')(i)?.0;
            let i = space1(i)?.0;
            let i = type_(i)?.0;
            let i = space1(i)?.0;
            let (i, name) = global(i)?;
            let i = many1(|i| {
                let i = char(',')(i)?.0;
                let i = space1(i)?.0;
                let i = type_(i)?.0;
                let i = space1(i)?.0;
                digit1(i)
            })(i)?
            .0;
            Ok((i, name))
        },
        char(')'),
    )(i)?;
    Ok((i, GetElementPtr(name.0)))
}

fn name(i: &str) -> IResult<&str, &str> {
    alt((map(string, |s| s.0), map(ident, |i| i.0), digit1))(i)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Function<'a>(pub &'a str);

fn function(i: &str) -> IResult<&str, Function> {
    let i = char('@')(i)?.0;
    let (i, name) = name(i)?;
    Ok((i, Function(name)))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Alias<'a>(&'a str);

fn alias(i: &str) -> IResult<&str, Alias> {
    let i = char('%')(i)?.0;
    let (i, name) = name(i)?;
    Ok((i, Alias(name)))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct String<'a>(&'a str);

// NOTE this will accept things that are not valid in LLVM-IR but we are only dealing with
// well-formed LLVM-IR so this is good enough
fn string(i: &str) -> IResult<&str, String> {
    let i = char('"')(i)?.0;
    let (i, x) = take_until("\"")(i)?;
    let i = char('"')(i)?.0;
    Ok((i, String(x)))
}

#[cfg(test)]
mod tests {
    use super::{Alias, Comment, FnSig, GetElementPtr, Ident, Local, String, Type};

    #[test]
    fn alias() {
        assert_eq!(
            super::alias("%\"blue_pill::ItmLogger\""),
            Ok(("", Alias("blue_pill::ItmLogger")))
        );

        assert_eq!(
            super::alias("%ExceptionFrame"),
            Ok(("", Alias("ExceptionFrame")))
        );

        assert_eq!(super::alias("%value"), Ok(("", Alias("value"))));
    }

    #[test]
    fn attribute() {
        assert!(super::attribute("void").is_err());
    }

    #[test]
    fn bitcast() {
        super::bitcast("bitcast (i8* getelementptr inbounds (<{ [228 x i8] }>, <{ [228 x i8] }>* @_ZN17at28c_rs_firmware3APP7usb_dev17h0475a05cee83d665E, i32 0, i32 0, i32 44) to i32*)").unwrap();
    }

    #[test]
    fn comment() {
        assert_eq!(
            super::comment("; core::ptr::real_drop_in_place"),
            Ok(("", Comment)),
        );

        assert_eq!(
            super::comment("; Function Attrs: norecurse nounwind readnone"),
            Ok(("", Comment)),
        );
    }

    #[test]
    fn getelementptr() {
        assert_eq!(
            super::getelementptr("getelementptr inbounds (<{ [0 x i8] }>, <{ [0 x i8] }>* @anon.3751ff68b49c735a867036886cf6a576.71, i32 0, i32 0)"),
            Ok(("", GetElementPtr(Some("anon.3751ff68b49c735a867036886cf6a576.71")))),
        );
    }

    #[test]
    fn ident() {
        assert_eq!(super::ident("__sbss"), Ok(("", Ident("__sbss"))));
        assert_eq!(
            super::ident("__EXCEPTIONS"),
            Ok(("", Ident("__EXCEPTIONS")))
        );

        // NOTE trailing space
        assert_eq!(
            super::ident("ExceptionFrame "),
            Ok((" ", Ident("ExceptionFrame")))
        );

        assert!(super::ident("\"foo\"").is_err());
        assert!(super::ident("0foo").is_err());
    }

    #[test]
    fn local() {
        assert_eq!(super::local("%113"), Ok(("", Local)));

        assert_eq!(super::local("%."), Ok(("", Local)));

        assert_eq!(super::local("%.9"), Ok(("", Local)));

        assert_eq!(super::local("%f"), Ok(("", Local)));

        assert_eq!(super::local("%_17.0.i.i.i.i.i"), Ok(("", Local)));
    }

    #[test]
    fn fmt_sig() {
        assert_eq!(
            FnSig {
                inputs: vec![],
                output: None,
            }
            .to_string(),
            "void ()"
        );

        assert_eq!(
            FnSig {
                inputs: vec![Type::Integer(8)],
                output: None,
            }
            .to_string(),
            "void (i8)"
        );

        assert_eq!(
            FnSig {
                inputs: vec![Type::Integer(8)],
                output: Some(Box::new(Type::Integer(8))),
            }
            .to_string(),
            "i8 (i8)"
        );
    }

    #[test]
    fn string() {
        assert_eq!(
            super::string(r#""\E3\81\93\E3\82\93\E3\81\AB\E3\81\A1\E3\82\8F""#),
            Ok((
                "",
                String(r#"\E3\81\93\E3\82\93\E3\81\AB\E3\81\A1\E3\82\8F"#)
            )),
        );

        assert_eq!(
            super::string(r#""Hello, world!""#),
            Ok(("", String("Hello, world!")))
        );

        // "\"He\nllo\""
        assert_eq!(
            super::string(r#""\22He\0Allo\22""#),
            Ok(("", String(r#"\22He\0Allo\22"#)))
        );

        // NOTE trailing space
        assert_eq!(super::string(r#""Hello" "#), Ok((" ", String("Hello"))));
    }
}
