#![type_length_limit = "16777216"] // see fire occurance of `fn attributes<'a>()`
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

// fn the_letter_a(input: &str) -> Result<(&str, ()), &str> {
//     match input.chars().next() {
//         Some('a') => Ok((&input['a'.len_utf8()..], ())),
//         _ => Err(input),
//     }
// }

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

// fn match_literal(expected: &'static str) -> impl Fn(&str) -> Result<(&str, ()), &str> {
//     move |input| match input.starts_with(expected) {
//         true => Ok((&input[expected.len()..], ())),
//         _ => Err(input),
//     }
// }

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

// fn identifier(input: &str) -> Result<(&str, String), &str> {
//     let mut matched = String::new();
//     let mut chars = input.chars();

//     match chars.next() {
//         Some(next) if next.is_alphabetic() => matched.push(next),
//         _ => return Err(input),
//     }

//     while let Some(next) = chars.next() {
//         if next.is_alphanumeric() || next == '-' {
//             matched.push(next);
//         } else {
//             break;
//         }
//     }

//     let next_index = matched.len();
//     Ok((&input[next_index..], matched))
// }

/// We're closing in on being able to use that Element struct defined at the
/// start of the module. We need to be able to combine our parsers together so
/// that we can carry over matches and feed the leftover inputs into the next
/// one.

/// We're going to do this using a parser combinator, a function that takes two
/// parsers and combines them into a new one.

/// Like every other new function in this excercise, we start with the types.
/// We've got two parsers and two results. Each parser takes a&Str input and
/// returns a `Result` pair of `(result, remaining input)` or an `Error`.

/// The critical difference lies in the result types. P1 returns R1, and P2
/// returns R2, such that the final parser returns (R1, R2). These are
/// Evaluated sequentially -- P1 first, then carry over the result and run P2
/// on any leftover input. Finally, return (R1, R2).

/// In the event of an error anywhere in the combinator we return immedietly
/// with that error.

// fn pair<P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Fn(&str) -> Result<(&str, (R1, R2)), &str>
// where
//     P1: Fn(&str) -> Result<(&str, R1), &str>,
//     P2: Fn(&str) -> Result<(&str, R2), &str>,
// {
//     move |input| match parser1(input) {
//         Ok((next_input, result1)) => match parser2(next_input) {
//             Ok((final_input, result2)) => Ok((final_input, (result1, result2))),
//             Err(err) => Err(err),
//         },
//         Err(err) => Err(err),
//     }
// }

/// Now that we can combine two parsers, how do we combine more? If we look
/// strictly at Type signatures, `pair` cannot be used with itself directly
/// even when we need two combinators but only care to keep one of the results.
/// Take the examples in our tests -- string literal matching is necessary for
/// finding the structure in the stream, but once we've parsed it we no longer
/// need it because that information is represented in our struct (`Element`)
/// directly. For the most obvious uses of pair, we will only car about one of
/// the two values but we need a way to tranform the return type, discarding
/// one side or the other.
///
/// Enter the `map` combinator, which takes a parser and a function that can
/// accepts the parser output and "map"s it to a new type.

/// This is a more complicated type than we've written so far, so break it down
/// because it explains exactly how this will work. `P` is the parser, `F` is
/// function that performs the transformation. `A` is the type we expect the
/// parser to output, and it must also be the type  that `F` accepts as input.
/// `B` is the output we expect from the function `F`, which of course is also
/// the final output of `map`

/// If the parser fails with an error, immedietly raise that up.

// fn map<P, F, A, B>(parser: P, map_fn: F) -> impl Fn(&str) -> Result<(&str, B), &str>
// where
//     P: Fn(&str) -> Result<(&str, A), &str>,
//     F: Fn(A) -> B,
// {
//     move |input| parser(input).map(|(next_input, result)| (next_input, map_fn(result)))
// }

/// This is a common pattern used all over the standard library, and it turns
/// out that Result implements this as well and we can use that in our
/// function. In Category Theory this is called a "functor". It has no general
/// form in Rust because Rust lacks higher kinded types, but it is useful and
/// can be seen implemented in `Result`, above, as well as `Iterator`, `Option`
/// and `Future`. Other languages, like Haskell, have a direct generalization.

/// Speaking of repeating patterns, this type signature keeps showing up:
/// `Fn(&Str) -> Result<(&str, Output), &str>`
/// We've been calling it the 'Parser' type signature. We can save ourselves
/// some typing and define a shorthand for it.

type ParseResult<'a, Output> = Result<(&'a str, Output), &'a str>;

/// Now we've got a shorthand, `ParseResult<_>`, and we can replace `_` with am
/// expected type, `String` or whatever. Typically you would avoid using the
/// lifetime `'a` here unless rustc complained. We need it in this case to use
/// in the Parser trait, below:

trait Parser<'a, Output> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, Output>;
}

/// We can now implement this for any function that matches the signature of a
/// parser. We can now pass around functions matching the type, and maybe even
/// other kinds of types eventually.

impl<'a, F, Output> Parser<'a, Output> for F
where
    F: Fn(&'a str) -> ParseResult<Output>,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, Output> {
        self(input)
    }
}

/// Let's rewrite `map` using this new trait. For posterity, we'll comment out
/// the old implementation. We'll use this pattern going forward for all
/// rewritten functions.

/// This is a bit simpler. We don't rewrite the type signature so many times.
/// One quirk, though, is that we can longer directly call `parser`. Since
/// the trait prescribes an interface, we need to adhere to it.

fn map<'a, P, F, A, B>(parser: P, map_fn: F) -> impl Parser<'a, B>
where
    P: Parser<'a, A>,
    F: Fn(A) -> B,
{
    move |input| {
        parser
            .parse(input)
            .map(|(next_input, result)| (next_input, map_fn(result)))
    }
}

/// Let's rewrite pair the same way.

/// The trait changes are straightforward once we adjust to the new interface.
/// Refactoring the function body is a little trickier because unlike `map` we
/// want to transform the contents of the `Result` instead of `Result` itself.
/// This code eschews all the matching of the earlier implementation, but is
/// identical in effect.

fn pair<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, (R1, R2)>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    move |input| {
        parser1.parse(input).and_then(|(next_input, result1)| {
            parser2
                .parse(next_input)
                .map(|(last_input, result2)| (last_input, (result1, result2)))
        })
    }
}

/// With our new `map` function and the refactored pair method, we can write
/// other useful combinators succinctly. The type signature is longer than the
/// function body.

fn left<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R1>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    map(pair(parser1, parser2), |(left, _)| left)
}

fn right<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R2>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    map(pair(parser1, parser2), |(_, right)| right)
}

/// We also need to update `match_literal` and `identifier` to use the new
/// trait and type, `Parse` and `ParseResult`.

fn match_literal<'a>(expected: &'static str) -> impl Parser<'a, ()> {
    move |input: &'a str| match input.starts_with(expected) {
        true => Ok((&input[expected.len()..], ())),
        _ => Err(input),
    }
}

fn identifier(input: &str) -> ParseResult<String> {
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

/// Whitespace
/// There are several places where we will have one or more spaces. Tehere are
/// a few 'one or more' definitions, which smells like an opportunity

/// Abstracting the above 'identifier' method yields a reusable form. Instead
/// of a single `A` we expext an arbitrary `Vec<A>`. We check for a single
/// result and then greedily consume as until there are no more and return the
/// vector of all results.

fn one_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input| {
        let mut result = Vec::new();

        if let Ok((next_input, first_item)) = parser.parse(input) {
            input = next_input;
            result.push(first_item);
        } else {
            return Err(input);
        }

        while let Ok((next_input, next_item)) = parser.parse(input) {
            input = next_input;
            result.push(next_item);
        }

        Ok((input, result))
    }
}

/// We could also user zero or more. This is very similar to one_or_more with
/// the initial check removed. There's basically no way for this to return an
/// error.
///
/// We cannot really dry out these functions easily because of the borrow
/// checker. The problem here is our mutable `input` variable, which is owned
/// and cannot be passed twice, so we cannot express one of these with the
/// other. We could write a `RangeBound` combinator that easily lets us
/// define at least n, exactly n, at most n, etc. relationships. Or we could
/// work out some Rc workaround to the borrow checker... but parsers really
/// only need these two functions. We shouldn't need to abstract this further,
/// and we can come back to this later if we do. Premature optimization.

fn zero_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input| {
        let mut result = Vec::new();

        while let Ok((next_input, next_item)) = parser.parse(input) {
            input = next_input;
            result.push(next_item);
        }

        Ok((input, result))
    }
}

/// So now let's look at how to parse out attributes.
/// If there are no attributes there may be valid streams without whitespace.
/// If there are any attributes, there must be whitespace, and if there are
/// multiple attributes there must be whitespace between attributes. We can
/// express this using our new combinators precisely -- we are looking for
/// zero or more occurences of one or more whitespace items followed by an
/// attribute.

/// We'll start with a whitespace parser.
/// Whitespace is more than just an empty space character. It also includes
/// line breaks, tabs, and a wide variety of Unicode points that render empty.
/// The standard library is here to help, though, as `char` has several methods
/// that will be useful: `is_whitespace`, `is_alphabetic`, `is_alphanumeric`.

/// We could use this to write something like `identifier`, but even saying
/// that is a sign we could probably abstract out a predicate combinator and
/// express both ideas using it. Start with a character parser:

fn any_char(input: &str) -> ParseResult<char> {
    match input.chars().next() {
        Some(next) => Ok((&input[next.len_utf8()..], next)),
        _ => Err(input),
    }
}

/// Now a `pred`icate combinator. This should look really familiar at this point.

fn pred<'a, P, A, F>(parser: P, predicate: F) -> impl Parser<'a, A>
where
    P: Parser<'a, A>,
    F: Fn(&A) -> bool,
{
    move |input| {
        if let Ok((next_input, value)) = parser.parse(input) {
            if predicate(&value) {
                return Ok((next_input, value));
            }
        }
        Err(input)
    }
}

/// A whitespace parser should be a quick one-liner now:

fn whitespace_char<'a>() -> impl Parser<'a, char> {
    pred(any_char, |c| c.is_whitespace())
}

/// These parsers only capture a single character, now, so let's build out the
/// additional combinators that we need.

fn space1<'a>() -> impl Parser<'a, Vec<char>> {
    one_or_more(whitespace_char())
}

fn space0<'a>() -> impl Parser<'a, Vec<char>> {
    zero_or_more(whitespace_char())
}

/// let's try to build an attribute parser from these tools, now. Unfortunately
/// a bottom up mess of combinators like this can be tricky to build and read.
/// The outermost `map` is the last step. We match an opening quote, but its
/// structural and so only care about the bit that follows the quote. That is
/// returned from the `left` combinator, because after the initial match we
/// need to parse the string contents until we come up against the structural
/// closing quote. We don't need to capture it, so we only care about the
/// `left` side of that. This isn't enough, though, because our `*_or_more`
/// parsers return vectors of matches. `map` is used to transform these into
/// the string we expect.

fn quoted_string<'a>() -> impl Parser<'a, String> {
    map(
        right(
            match_literal("\""), // escaped single "
            left(
                zero_or_more(pred(any_char, |c| *c != '"')),
                match_literal("\""),
            ),
        ),
        |char| char.into_iter().collect(),
    )
}

/// now we parse attribute pairs
/// the structure of this code is almost declarative in how it reads

fn attribute_pair<'a>() -> impl Parser<'a, (String, String)> {
    pair(identifier, right(match_literal("="), quoted_string()))
}

/// again, almost declarative now
fn attributes<'a>() -> impl Parser<'a, Vec<(String, String)>> {
    zero_or_more(right(space1(), attribute_pair()))
}

/// #![type_length_limit = "16777216"]
/// the compiler is nearing a limit on the number of types. rustc gives pretty
/// good advice. We go one step further here and increase the limit 2^24 as
/// suggested by Bodil. It seems as good as any other. I can't find an upper
/// limit in the rustc docs.

/// Let's add some unit tests
/// For whatever reason I decided that tests exist outside of the continuity
/// the doc and I've lumped them all at the bottom here, in order.

/// Build one parser and then verify three properties
/// 1. If the string doesn't start with the literal, return an error
/// 2. If the string starts with the literal, it should strip the match off
/// 3. If the string starts with the literal, it should return the remainder

#[test]
fn literal_parser() {
    let parse_atcq = match_literal("A Tribe Called Quest");
    assert_eq!(Ok(("", ())), parse_atcq.parse("A Tribe Called Quest"));
    assert_eq!(
        Ok((" has got it from here", ())),
        parse_atcq.parse("A Tribe Called Quest has got it from here")
    );
    assert_eq!(
        Err("You gotta say the whole thing"),
        parse_atcq.parse("You gotta say the whole thing"),
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

/// with our new combinator, we can parse more sophisticated inputs
/// 1. return an identifier from a well formed tag
/// 2. error if P1 has an error (cannot match literal)
/// 3. error if P2 has an error (malformed Identifier)

#[test]
fn pair_combinator() {
    let tag_opener = pair(match_literal("<"), identifier);
    assert_eq!(
        Ok(("/>", ((), "bad-bad-not-good".to_string()))),
        tag_opener.parse("<bad-bad-not-good/>")
    );
    assert_eq!(Err("bbng"), tag_opener.parse("bbng"));
    assert_eq!(Err("!bbng"), tag_opener.parse("<!bbng"));
}

/// now add some tests for our new functors, right and left
/// 1. happy path
/// 2. error in P1
/// 3. error in P2

#[test]
fn right_combinator() {
    let tag_opener = right(match_literal("<"), identifier);
    assert_eq!(
        Ok(("/>", "de-la-soul".to_string())),
        tag_opener.parse("<de-la-soul/>")
    );
    assert_eq!(Err("missing-carrot>"), tag_opener.parse("missing-carrot>"));
    assert_eq!(
        Err("!cannot-start-with-symbol>"),
        tag_opener.parse("<!cannot-start-with-symbol>")
    );
}

#[test]
fn left_combinator() {
    let tag_opener = left(identifier, match_literal("/>"));
    assert_eq!(
        Ok(("", "de-la-soul".to_string())),
        tag_opener.parse("de-la-soul/>")
    );
    assert_eq!(Err(">"), tag_opener.parse("missing-close>"));
    assert_eq!(
        Err("!cannot-start-with-symbol>"),
        tag_opener.parse("!cannot-start-with-symbol>")
    );
}

/// multiple parser combinator tests
/// 1. happy path
/// 2. a bad start should be an error even if the string shows up later
/// 3. an empty string should be an error since it must match at least 1 time

#[test]
fn one_or_more_combinator() {
    let parser = one_or_more(match_literal("ha"));
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Err("ahah"), parser.parse("ahah"));
    assert_eq!(Err(""), parser.parse(""));
}

/// 1. happy path
/// 2. a bad start return the whole string without grabbing anything later
/// 3. an empty string is fine, too

#[test]
fn zero_or_more_combinator() {
    let parser = zero_or_more(match_literal("ha"));
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Ok(("ahah", vec![])), parser.parse("ahah"));
    assert_eq!(Ok(("", vec![])), parser.parse(""));
}

/// create a parser that looks for a single char predicate
/// 1. happy path
/// 2. obvious error
/// 3. the predicate parser captures only a single char

#[test]
fn predicate_combinator() {
    let parser = pred(any_char, |c| *c == 'o');
    assert_eq!(Ok(("mg", 'o')), parser.parse("omg"));
    assert_eq!(Err("lol"), parser.parse("lol"));
    assert_eq!(Ok(("okta", 'o')), parser.parse("ookta"));
}

/// quoted

#[test]
fn quoted_string_parser() {
    assert_eq!(
        Ok(("", "Hello Joe!".to_string())),
        quoted_string().parse("\"Hello Joe!\"")
    );
}

/// attributes

#[test]
fn attribute_parser() {
    assert_eq!(
        Ok((
            "",
            vec![
                ("one".to_string(), "1".to_string()),
                ("two".to_string(), "2".to_string())
            ]
        )),
        attributes().parse(" one=\"1\" two=\"2\"")
    );
}