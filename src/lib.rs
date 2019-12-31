/// a simple parser combinator excercise
///
/// based on [Bodil Stokke](https://bodil.lol/)'s 
/// [blog post](https://bodil.lol/parser-combinators/) on the same topic.
/// 
/// We're assuming rustc version 1.34.0 or later using Rust 2018, as laid out 
/// in the Cargo.toml
///
/// We're going to write a parser for the Xcruciating Markup Language. It's a
/// simplified XML without namespaces, validation, etc. He's an example:
///
/// ```xml
/// <parent-element>
///  <single-element attribute="value" />
/// </parent-element>
/// ```
///
/// Elements start with a `<`, then an Identifier, defined below. This
/// is followed by whitespace, an optional list of Attribute Pairs, and either
/// closing `/>` to signify a childless element or a `>` to signify a sequence
/// of child elements following. After the child elements there may be
/// additional whitespace, then a closing tag comprised of the `</` symbol,
/// an identifier matching thee opening tag, and a final `>`.
///
/// Identifiers start with a letter, followed by an arbitrary number of
/// letters, numbers, and `-` symbols.
///
/// Attribute Pairs start with an Identifier, followed by an `=` and a double
/// quoted string. For this parser there will be no escape quotes or single
/// quotes or any other quotidian nonsense.
///
/// resources:
///  * [Phil WAdler's Paper](https://homepages.inf.ed.ac.uk/wadler/papers/marktoberdorf/baastad.pdf)
///  * [pom - an industrial version of this approach](https://crates.io/crates/pom)
///  * [nom - most popular parser combinator](https://crates.io/crates/nom)
///  * [combine - a third take on parser combinators in rust](https://crates.io/crates/combine)
///  * [parsec - Haskell, but the definitive industrial parser combinator](http://hackage.haskell.org/package/parsec)

#[derive(Clone, Debug, PartialEq, Eq)]
struct Element {
    name: String,
    attributes: Vec<(String, String)>,
    children: Vec<Element>,
}