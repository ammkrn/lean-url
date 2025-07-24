
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser
import LeanUrl.Parser.Basic

open Lean (ToJson FromJson)

/-
see: https://github.com/web-platform-tests/wpt/tree/befe66343e5f21dc464c8c772c6d20695936714f/url
-/
structure TestCase where
  input : String
  failure: Option Bool
  base: Option String
  href : Option String
  origin : Option String
  protocol : Option String
  username : Option String
  password : Option String
  host : Option String
  hostname : Option String
  port : Option String
  pathname : Option String
  search : Option String
  hash : Option String
  relativeTo : Option String
deriving ToJson, FromJson, Repr, Inhabited

/-
Not as easy as just parsing an array; the example file occasionally interrupts the objects
with strings describing the subsequent objects.
-/
def processElems (xs : Lean.Json) : IO (Array (String × Array TestCase)) := do
  match xs with
  | .arr xs =>
    /- (test set description : String × TestCases) -/
    let mut out := #[]
    let mut description := ""
    let mut cur := #[]
    for x in xs do
      match x with
      | .str s' =>
        out := out.push (description, cur)
        cur := #[]
        description := s'
      | .obj _ =>
        match FromJson.fromJson? x with
        | .error e => throw (IO.userError e)
        | .ok a => cur := cur.push a
      | _ => throw (IO.userError "not string or object")
    return out
  | _ => throw (IO.userError "not an array")

structure Output where
  total : Nat
  parseFail : Nat
  parseFailures : Std.HashMap String  (Nat × Bool × String)
  eqFail : Nat
  eqFailures : Std.HashMap String (Nat × Bool × String)
deriving Inhabited, Repr

def runTests : IO Output := do
  let path := System.mkFilePath ("Tests/urltestdata.json".split (fun c => c == '/'))
  let file ← IO.FS.readFile path
  let testCases ←
    match (Lean.Json.parse file).map processElems with
    | .ok xs => xs
    | .error e => throw (IO.userError e)

  let mut output : Output := Inhabited.default

  for ((descr, testCases), idx) in testCases.zipIdx do
    output := { output with total := output.total + testCases.size }
    for testCase in testCases do
      let shouldFail := testCase.failure.getD false
      let parseResult := LeanUrl.Parser.parseUrl testCase.input testCase.base
      match parseResult, shouldFail with
      | .error _e _, true => continue
      | .error e _, false => output := {
        output with
        parseFail := output.parseFail + 1
        parseFailures := output.parseFailures.insert descr (idx, shouldFail, e)
      }
      | .ok _a _, true =>
            output := {
              output with
              parseFail := output.parseFail + 1
              parseFailures := output.parseFailures.insert descr (idx, shouldFail, "")
            }
      | .ok a _, false =>
        if (a.serialize false) != testCase.href.get!
        then output := {
          output with
          eqFail := output.eqFail + 1
          eqFailures := output.eqFailures.insert descr (idx, shouldFail, "")
        }
  return output


-- 61 failures remaining, mostly from IDNA.
#eval runTests
--#eval '\uFDD0'
