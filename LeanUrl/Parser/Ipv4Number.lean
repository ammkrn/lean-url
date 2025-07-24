import LeanUrl.Util
import LeanUrl.Parser.Util

namespace LeanUrl.Parser.Ipv4Number

structure State where
  input : Array Char
  pointer : Nat
  errorLog : Array SyntaxViolationLog

open SyntaxViolation

def curr? : EStateM SyntaxViolationLog State (Option Char) := fun s =>
  .ok s.input[s.pointer]? s

def peek1? : EStateM SyntaxViolationLog State (Option Char) := fun s =>
  .ok s.input[s.pointer+1]? s

def hasNext : EStateM SyntaxViolationLog State Bool := do
  return (← peek1?).isSome

def parseHex (s : Subarray Char) : Except String Nat := do
  let mut out := 0
  for c in s do
    match hexDigitToNat? c with
    | none => throw s!"not a hex digit {c}"
    | some n =>
      out := out * 16
      out := out + n
  return out

def parseOctal (s : Subarray Char) : Except String Nat := do
  let mut out := 0
  for c in s do
    match c.octalToNat? with
    | none => throw s!"not an octal digit {c}"
    | some n =>
      out := out * 8
      out := out + n
  return out

def startsWith' (c : Char) : EStateM SyntaxViolationLog State Bool := fun s =>
  if s.input[0]? == some '0'
  then
    let x := s.input[1]?
    .ok (x == c.toLower || x == c.toUpper) s
  else
    .ok false s

def restAsNat (radix : Nat) : EStateM SyntaxViolationLog State Nat := do
  match radix with
  | 10 =>
    let mut out := 0
    for c in (← get).input[(← get).pointer:] do
      if c.isDigit
      then
        out := (out * 10) + (c.toNat - '0'.toNat)
      else
        throw (ipv4NonNumericPart, none, some "bad decimal")
    return out
  | 8 =>
    let slice := (← get).input[(← get).pointer:]
    match parseOctal slice with
    | .ok out => return out
    | .error e =>
    throw (ipv4NonNumericPart, none, some s!"{e}, {sourceLoc!}")
  | 16 =>
    let slice := (← get).input[(← get).pointer:]
    match parseHex slice with
    | .ok out => return out
    | .error e =>
    throw (ipv4NonNumericPart, none, some s!"{e}, {sourceLoc!}")
  | owise => throw (ipv4NonNumericPart, none, some s!"owise {owise}")


def parse' : EStateM SyntaxViolationLog State (Nat × Bool) := do
  if (← get).input.isEmpty then throw (ipv4EmptyPart, none, none)
  let mut validationError := false
  let mut r := 10
  let s := (← get).input
  if s.size ≥ 2 && (← startsWith' 'x')
  then
    validationError := true
    modify fun st => { st with pointer := st.pointer + 2 }
    r := 16
  else if s.size ≥ 2 && (s[0]? == some '0')
  then
    validationError := true
    modify fun st => { st with pointer := st.pointer + 1 }
    r := 8
  if (← curr?).isNone then return (0, true)
  let output ← restAsNat r
  return (output, validationError)

def parse (input: Array Char) : Except SyntaxViolationLog (Nat × Bool) :=
  match parse'.run { input, pointer := 0, errorLog := #[] } with
  | .ok a _ => .ok a
  | .error e _ => .error e
