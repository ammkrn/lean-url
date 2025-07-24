import Lean
import Lake

open Lean

def Char.isASCIIHexDigit (c : Char) : Bool :=
  ('0' ≤ c ∧ c ≤ '9') || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F')

def Char.isForbiddenHostCodePoint : Char → Bool
  | '\u0000' | '\u0009' | '\u000A' | '\u000D' | '\u0020'
  | '\u0023' | '\u002F' | '\u003A' | '\u003C' | '\u003E'
  | '\u003F' | '\u0040' | '\u005B' | '\u005C' | '\u005D'
  | '\u005E' | '\u007C' => true
  | _ => false

def Char.octalToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '7' then
    some (c.toNat - '0'.toNat)
  else
    none

def hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else
    let c := c.toLower
    if 'a' ≤ c ∧ c ≤ 'f' then
      some (c.toNat - 'a'.toNat + 10)
    else
      none

def UInt32.isAscii (n : UInt32) : Bool := n ≤ 0x7f

def Char.isAscii (c : Char) : Bool := c.val.isAscii

def Char.isSurrogate (c : Char) : Bool :=
  '\uD800' ≤ c && c ≤ '\uDFFF'

def Char.isNoncharacter (c : Char) : Bool :=
  (c.val ≤ 0xfdef && 0xfdd0 ≤ c.val) ||
  (((c.val &&& 0xffff) == 0xfffe) || ((c.val &&& 0xffff) == 0xffff))

/-
The URL code points are ASCII alphanumeric, U+0021 (!), U+0024 ($), U+0026 (&), U+0027 ('),
 U+0028 LEFT PARENTHESIS, U+0029 RIGHT PARENTHESIS, U+002A (*), U+002B (+), U+002C (,),
  U+002D (-), U+002E (.), U+002F (/), U+003A (:), U+003B (;), U+003D (=), U+003F (?),
  U+0040 (@), U+005F (_), U+007E (~),
  and code points in the range U+00A0 to U+10FFFD, inclusive, excluding surrogates and noncharacters.
-/
def Char.isUrlCodePoint : Char → Bool
  | '\u0021' | '\u0024' | '\u0026' | '\u0027'
  | '\u0028' | '\u0029' | '\u002A' | '\u002B'
  | '\u002C' | '\u002D' | '\u002E' | '\u002F'
  | '\u003A' | '\u003B' | '\u003D' | '\u003F'
  | '\u0040' | '\u005F' | '\u007E' => true
  | owise =>
    owise.isAlphanum ||
    ('\u00A0' ≤ owise && owise.val ≤ 0x10FFFD && !owise.isSurrogate && !owise.isNoncharacter)

def Char.isC0Control (c : Char) : Bool := c ≤ '\u001F'

/--
A forbidden domain code point is a forbidden host code point, a C0 control, U+0025 (%), or U+007F DELETE.
-/
def Char.forbiddenDomainCodePoint : Char → Bool
  | '\u0025' | '\u007f' => true
  | owise => owise.isForbiddenHostCodePoint || owise.isC0Control

def String.startsWithWindowsDriveLetter (s : String) : Bool :=
  s.length >= 2
  && Char.isAlpha (s.get ⟨0⟩)
  && (s.get ⟨1⟩ == ':' || s.get ⟨1⟩ == '|')
  && (s.length == 2 ||
      let c := s.get ⟨2⟩
      c == '/' || c == '\\' || c == '?' || c == '#')

def String.isWindowsDriveLetter (segment : String) : Bool :=
  segment.length == 2 && startsWithWindowsDriveLetter segment

def String.isNormalizedWindowsDriveLetter (segment : String) : Bool :=
  isWindowsDriveLetter segment && segment.get ⟨1⟩ == ':'

def Char.c0ControlOrSpace (c : Char) : Bool :=
  c ≤ '\u0020'

theorem Char.c0ControlOrSpace_eq (c : Char) : (c.c0ControlOrSpace) = (c ≤ ' ') := by
  simp [Char.c0ControlOrSpace]

def Char.tabOrNewline (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\r'

def String.beqIgnoreAsciiCase (s₁ s₂ : String) : Bool := s₁.toLower == s₂.toLower

def isSingleDotURLPathSegment (s : String) : Bool :=
  s == "." || s.beqIgnoreAsciiCase "%2e"

def isDoubleDotURLPathSegment (s : String) : Bool :=
  s == ".." || s.beqIgnoreAsciiCase ".%2e" || s.beqIgnoreAsciiCase "%2e." || s.beqIgnoreAsciiCase "%2e%2e"

def String.toArray (s : String) : Array Char :=
  s.foldl (fun a c => a.push c) #[]

def Array.toString (cs : Array Char) : String :=
  cs.foldl (fun s c => s.push c) ""

def Subarray.toString (cs : Subarray Char) : String :=
  cs.foldl (fun s c => s.push c) ""

/--
whatwg "strict split" implementation
-/
def strictSplit (xs : Array Char) (delim : Char) : Array (String) := Id.run do
  let mut pos := 0
  let mut tokens : Array String := #[]
  let collect (pos : Nat) : (String × Nat) := Id.run do
    let mut result := ""
    let mut pos := pos
    while pos < xs.size && xs[pos]? != some delim do
      result := result.push xs[pos]!
      pos := pos + 1
    return (result, pos)
  let (tok, pos') := collect pos
  tokens := tokens.push tok
  pos := pos'
  while pos < xs.size do
    assert! xs[pos]! == delim
    pos := pos + 1
    let (tok, pos') := collect pos
    tokens := tokens.push tok
    pos := pos'
  return tokens

elab "line!" : term => do
  return toExpr (← Lean.getRefPosition).line

elab "column!" : term => do
  return toExpr (← Lean.getRefPosition).column

elab "module!" : term => do
  return toExpr (toString (← getEnv).mainModule)

elab "sourceLoc!" : term => do
  let module := (← getEnv).mainModule
  let line := (← Lean.getRefPosition).line
  let col := (← Lean.getRefPosition).column
  let s := s!"{module}:{line}:{col}"
  return toExpr s
