# lean-url 

A library implementing URLs (aka URIs/IRIs) and their API according to the whatwg [URL spec](https://url.spec.whatwg.org) in [Lean 4](https://lean-lang.org/).

This library uses the term "URL" rather than "URI" for the same reason(s) as the whatwg spec: "URI and IRI are just confusing. In practice a single algorithm is used for both so keeping them distinct is not helping anyone. URL also easily wins the search result popularity contest."

## TODO

+ IDNA, punycode, etc. (see LeanUrl/Parser/Unicode.lean). The current implementation of `domainToUnicode` is effectively a placeholder.

+ Support for non-UTF8 encodings.

+ There is currently a significant amount of low hanging fruit in terms of efficiency gains.

## Examples:

```
import LeanUrl.Parser.Basic

open LeanUrl.Parser

-- URL parsing

/-
Except.ok {
  scheme := "http",
  username := some "user",
  password := some "pass",
  host := some (LeanUrl.Host.domain { val := "foo", h := _ }),
  port := some 21,
  path := Sum.inr #["bar;par"],
  query := some "b",
  fragment := some "c",
  blobUrlEntry := none
}
-/
#eval LeanUrl.Parser.parseUrl' "http://user:pass@foo:21/bar;par?b#c" (base := none)

/-
Except.ok {
  scheme := "http",
  username := some "user",
  password := some "pass",
  host := some (LeanUrl.Host.domain { val := "foo", h := _ }),
  port := some 21,
  path := Sum.inr #["bar;par"],
  query := some "b",
  fragment := some "c",
  blobUrlEntry := none
}
-/
#eval LeanUrl.Parser.parseUrl'
  (input := "http://user:pass@foo:21/bar;par?b#c")
  (base := some "http://example.org/foo/bar")

-- URL serialization

/-- info: Except.ok "file://host/C:" -/
#guard_msgs in #eval
  (parseUrl'
    (input := "C|")
    (base := "file://host/D:/dir1/dir2/file")
  ).map (fun url => url.serialize false)

/-- info: Except.ok "http://255.255.255.255/" -/
#guard_msgs in #eval
  (parseUrl'
    (input := "http://0xffffffff")
    (base := "http://other.com/")
  ).map (fun url => url.serialize false)
```




