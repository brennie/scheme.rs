use std::{
    env,
    fs::File,
    io::{BufWriter, prelude::*},
    path::Path,
};

use failure::Error;

fn main() -> Result<(), Error> {
    write_keyword_map()?;

    Ok(())
}

fn write_keyword_map() -> Result<(), Error> {
    let path = Path::new(&env::var("OUT_DIR")?).join("keyword.codegen.rs");
    let mut file = BufWriter::new(File::create(&path)?);


    write!(&mut file, "#[allow(clippy::all)]\n")?;
    write!(&mut file, "static KEYWORDS: phf::Map<&'static str, Keyword> = ")?;

    phf_codegen::Map::new()
        .entry("quote", "Keyword::Quote")
        .entry("lambda", "Keyword::Lambda")
        .entry("if", "Keyword::If")
        .entry("set!", "Keyword::Set")
        .entry("begin", "Keyword::Begin")
        .entry("cond", "Keyword::Cond")
        .entry("and", "Keyword::And")
        .entry("or", "Keyword::Or")
        .entry("case", "Keyword::Case")
        .entry("let", "Keyword::Let")
        .entry("let*", "Keyword::LetStar")
        .entry("letrec", "Keyword::LetRec")
        .entry("do", "Keyword::Do")
        .entry("delay", "Keyword::Delay")
        .entry("quasiquote", "Keyword::Quasiquote")
        .entry("else", "Keyword::Else")
        .entry("=>", "Keyword::RightArrow")
        .entry("define", "Keyword::Define")
        .entry("unquote", "Keyword::Unquote")
        .entry("unquote-splicing", "Keyword::UnquoteSplicing")
        .build(&mut file)?;

    write!(&mut file, ";\n")?;

    Ok(())
}
