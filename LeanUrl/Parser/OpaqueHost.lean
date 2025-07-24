import LeanUrl.Util
import LeanUrl.Percent.Basic
import LeanUrl.Parser.Util

namespace LeanUrl.Parser.OpaqueHost

open SyntaxViolation

def pctEncodeCk : List Char → Bool
  | [] => true
  | hd :: rest =>
    if hd == '\u0025'
    then
      match rest with
      | a :: b :: rest => a.isASCIIHexDigit && b.isASCIIHexDigit && pctEncodeCk rest
      | _ => false
    else
      pctEncodeCk rest

def parseAux : EStateM SyntaxViolationLog (Array Char) String := do
  let s ← get
  if s.any (·.isForbiddenHostCodePoint)
  then
    throw (hostInvalidCodePoint, none, none)
  if s.any (fun c => !c.isUrlCodePoint && !(c == '\u0025'))
  then
    throw (invalidUrlUnit, none, none)
  let asChars := (← get).toList
  if !(pctEncodeCk asChars)
  then
    throw (invalidUrlUnit, none, none)
  return LeanUrl.Percent.utf8PercentEncode s.toString LeanUrl.Percent.PercentEncodeSets.c0Controls

def parse (chars : Array Char) : Except SyntaxViolationLog String :=
  match parseAux.run chars with
  | .ok opaqueHost _ => .ok opaqueHost
  | .error e _ => .error e
