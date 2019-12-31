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

/// Parsers transform a stream of data by giving it structure.
/// 
/// Any given parser is going to be limited in it's capability. It may only
/// parse some of the input, and return unparsed input alongside parsed output.
/// If it can't parse any of it, we want to return an error.
///
/// Something like this:
/// ```
/// Fn(Input) -> Result<(Input, Output), Error>
/// ```
///
/// In implementation we need to be more precise for the compiler, so we'll
/// add some types.

/// Fn(&str) -> Result<(&str, Element), &str>

/// For the moment we're going to return problematic string slices instead of
/// real errors.

/// String slices are efficient pointers to a piece of a string. We can consume
/// the input in sub-slices and return the remainder.

/// Using a string slice gives us a lot of useful methods in Rust, though as
/// Bodil points out we could have used &[u8] instead here. This corresponds to
/// single ASCII characters and allows direct indexing of the slice. Unicode is
/// complicated, though, and we're going to leverage the standard lib to manage
/// it for us. Dealing with Unicode here would be something of a distraction
/// for this excercise but important to any industrial parser.


/// Let's begin with a parser examines the first character in the string and
/// extracts it, iff it is `a`

/// In this example we're not even using the Element struct since this parser
/// is ridiculously simple. It can only succeed in one case, so we return the
/// unit type `()` since the letter 'a' can be assumed. This is probably more
/// complicated than it's worth since it required a whole paragraph to explain
/// rather than just returning 'a', but I'm sticking to the original text for
/// now.

/// Anyhow, the intent was to let us focus on manipulating the input streams,
/// so let's just look at that. The standard library methods that we
/// anticipated needing above are the bread-and-butter of this parser.
/// We're letting it handle splitting the slice into an interator of chars and
/// so we can simply pull the 'next' item off of it.

/// Since the slice could be empty, what we get back is an `Option<char>`
/// which will contain the next `char` or a `None` if it's empty.

/// A `char` isn't as simple as it seems, though, because Unicode abstracts
/// over ... a lot. We could address this by messing directly with bytes as
/// discussed above, but instead let's do what almost every workaday programmer
/// does and pretend a Unicode `char` matches our ASCII-founded intuitions and
/// we'll ignore graphemes, clusters, scalars, and all the intermediary
/// abstractions between bytes and semantic value. Again, it's enough to know
/// that if we start accepting input written by other people we'll have to deal
/// with that stuff sooner or later. For this demo we can call it out of scope.

/// Pattern matching will do a lot of heavy lifting in our parser combinators.
/// It's no coincidence that Haskell also has advanced pattern matching and
/// one of it's greatest industry use cases is parsing. All Rust parsing libs
/// liberally use this language feature.

/// `Some('a')` is our specific result and matching against it directly keeps
/// our parser concise. If the character looks good, we'll return the rest of
/// the input, sans `a`. If there's no char or the character is not the
/// precise one we expect then we'll return an error. Not a useful error, so
/// that's something to improve.

/// This function isn't directly useful for our task, but it looks a lot like
/// the start of an element parser. We'll need to recognize several single
/// chars. It seems like we'll need this in a few places, which usually means
/// it's time for an abstraction.

fn the_letter_a(input: &str) -> Result<(&str, ()), &str> {
    match input.chars().next() {
        Some('a') => Ok((&input['a'.len_utf8()..], ())),
        _ => Err(input),
    }
}

/// We'll need to create functions like the one above to match not just single
/// chars but arbitrary static strings.

/// This next function doesn't look like the parser above. Instead it takes an
/// arg and returns something that looks like a parser, in that it accepts
/// input and then returns the `Result` we expect from a parser. We call this a
/// 'Higher Order' function, and in some ways it's comparable to a Factory that
/// you may have seen in a more object oriented language. Instead of objects
/// we're going to be creating and returning functions that are 'closed over'
/// some initial state we pass in when we call it to create the new function.

/// the body is similar but where we matched against a literal before we match
/// against a variable now.

fn match_literal(expected: &'static str) -> impl Fn(&str) -> Result<(&str, ()), &str> {
    move |input| match  input.starts_with(expected) {
        true => Ok((&input[expected.len()..], ())),
        _ => Err(input),
    }
}

/// Now that we can match literals we need to match element names. We don't
/// know this ahead of time. We could do it with a regex but pulling in a
/// whole crate seems like overkill.

/// Let's familiarize ourselves with the Identifier definition, again. Start
/// with an alphabetical character, then zero or more of either an
/// alphabetical, number, or `-` chars.

/// Start with the type. We don't need a closure because we're writing many
/// similar functions looking for strings known at compile time. This also
/// means we can no longer use the generic unit type to indicate a match --
/// since we don't know exactly what string we're matching ahead of time we
/// need to return the matched string containing the Identifier.

/// So we have to encode the rules of an Identifier in our algorithm. First up,
/// check to see if we have a letter. If it's not, fail out with an Error. This
/// isn't an Identifier. We use the standard library method here. Next, we
/// start building up our Identifier by pulling characters off the iterator and
/// pushing them into the Identifier if they match our criteria. When we find
/// one that doesn't match we're done parsing the identifier and we need to
/// break out of the loop and return that String we've been building up, along
/// with the remaining input.

/// Of course, at any time during this we could run out of chars and hit the
/// end of the input, which is also an Error.

fn identifier(input: &str) -> Result<(&str, String), &str> {
    let mut matched = String::new();
    let mut chars = input.chars();

    match chars.next() {
        Some(next) if next.is_alphabetic() => matched.push(next),
        _ => return Err(input),
    }

    while let Some(next) = chars.next() {
        if next.is_alphanumeric() || next == '-' {
            matched.push(next);
        } else {
            break;
        }
    }

    let next_index = matched.len();
    Ok((&input[next_index..], matched))
}

/// Let's add some unit tests

/// Build one parser and then verify three properties
/// 1. If the string doesn't start with the literal, return an error
/// 2. If the string starts with the literal, it should strip the match off
/// 3. If the string starts with the literal, it should return the remainder

#[test]
fn literal_parser() {
    let parse_atcq = match_literal("A Tribe Called Quest");
    assert_eq!(
        Ok(("", ())),
        parse_atcq("A Tribe Called Quest")
    );
    assert_eq!(
        Ok((" has got it from here", ())),
        parse_atcq("A Tribe Called Quest has got it from here")
    );
    assert_eq!(
        Err("You gotta say the whole thing"),
        parse_atcq("You gotta say the whole thing"),
    );
}

/// now lets check the identifier parser
/// 1. the identifier is greedy and consumes the input
/// 2. the identifier should return the remainder of the input
/// 3. the identifer should throw an error on an invalid identifier

#[test]
fn identifier_parser() {
    assert_eq!(
        Ok(("", "i-am-an-identifier".to_string())),
        identifier("i-am-an-identifier")
    );
    assert_eq!(
        Ok((" entirely an identifier", "not".to_string())),
        identifier("not entirely an identifier")
    );
    assert_eq!(
        Err("!not a valid identifier"),
        identifier("!not a valid identifier")
    )
}