import LeanUrl.Util
import LeanUrl.Parser.Util
import LeanUrl.Url.Basic

import Std.Net

namespace LeanUrl.Parser.Ipv6

structure State where
  pieceIndex : Nat
  compress : Option Nat
  numbersSeen : Nat
  address : Array Nat
  input : Array Char
  pointer : Nat
  swaps : Nat

open SyntaxViolation

def curr? : EStateM SyntaxViolationLog State (Option Char) := fun s =>
  .ok s.input[s.pointer]? s

def peek1? : EStateM SyntaxViolationLog State (Option Char) := fun s =>
  .ok s.input[s.pointer+1]? s

def hasNext : EStateM SyntaxViolationLog State Bool := do
  return (← peek1?).isSome

def parse' : EStateM SyntaxViolationLog State Unit := do
  /- 5. -/
  if (← curr?) == some '\u003A'
  then
    /- 5.1 -/
    if (← peek1?)!= some '\u003A' then throw (ipv6InvalidCompression, some (Int.ofNat (← get).pointer), none)
    /- 5.2, 5.3 -/
    modify fun s => { s with pointer := s.pointer + 2, pieceIndex := s.pieceIndex + 1, compress := s.pieceIndex }
  /- 6. -/
  while (← curr?).isSome do
    /- 6.1 -/
    if (← get).pieceIndex == 8 then throw (ipv6TooManyPieces, some (Int.ofNat (← get).pointer), none)
    /- 6.2 -/
    if (← curr?) == some '\u003A'
    then
      if (← get).compress.isSome then throw (ipv6MultipleCompressionValidationError, some (Int.ofNat (← get).pointer), none)
      modify fun s => { s with
        pieceIndex := s.pieceIndex + 1
        pointer := s.pointer + 1
        compress := some s.pieceIndex
      }
      continue
    /- 6.3 -/
    let mut value := 0
    let mut length := 0
    /- 6.4 -/
    while length < 4 do
      match (← curr?).bind hexDigitToNat? with
      | none => break
      | some digit =>
        value := value * 0x10 + digit
        length := length + 1
        modify (fun s => { s with pointer := s.pointer + 1 })

    let c? := (← curr?)
    /- 6.5 -/
    if c? == some '\u002E'
    then
      /- 6.5.1 -/
      if length = 0 then throw (ipv4InIpv6InvalidCodePoint, none, none)
      assert! (← get).pointer ≥ length
      /- 6.5.2 -/
      modify fun st => { st with pointer := st.pointer - length }
      /- 6.5.3 -/
      if (← get).pieceIndex > 6 then throw (ipv4InIpv6TooManyPieces, none, none)
      /- 6.5.4 -/
      modify fun st => { st with numbersSeen := 0 }
      /- 6.5.5 -/
      while (← curr?).isSome do
        let c := (← curr?).get!
        /- 6.5.5.1 -/
        let mut ipv4Piece := none
        /- 6.5.5.2 -/
        if (← get).numbersSeen > 0
        then
          if c == '\u002e' && (← get).numbersSeen < 4
          /- 6.5.5.5.1 -/
          then modify fun m => { m with pointer := m.pointer + 1 }
          /- 6.5.5.5.2 -/
          else throw (ipv4InIpv6InvalidCodePoint, none, none)
        /- 6.5.5.3 -/
        if !(((← curr?).map Char.isDigit).getD false) then throw (ipv4InIpv6InvalidCodePoint, none, none)
        /- 6.5.5.4 -/
        while (← curr?).isSome do
          let c := (← curr?).get!
          if !c.isDigit then break
          let number := c.toNat - 48
          /- 6.5.5.4.2 -/
          let _ ← match ipv4Piece with
          | none => ipv4Piece := some number
          | some 0 => throw (ipv4InIpv6InvalidCodePoint, none, none)
          | some owise => ipv4Piece := some ((10 * owise) + number)
          /- 6.5.5.4.3 -/
          if (ipv4Piece.map (fun x => (x > 255 : Bool))).getD false then throw (ipv4InIpv6OutOfRange, none, none)
          /- 6.5.5.4.4 -/
          modify fun m => { m with pointer := m.pointer + 1 }
        modify fun m => {
          m with
          /- 6.5.5.5 -/
          address := m.address.modify m.pieceIndex (fun x => (x * 0x100) + ipv4Piece.get!)
          /- 6.5.5.6 -/
          numbersSeen := m.numbersSeen + 1
        }
        /- 6.5.5.7 -/
        if (← get).numbersSeen == 2 || (← get).numbersSeen == 4
        then modify fun m => { m with pieceIndex := m.pieceIndex + 1}
      /- 6.5.6-/
      if (← get).numbersSeen != 4 then throw (ipv4InIpv6TooFewPieces, none, some sourceLoc!)
      /- 6.5.7 -/
      break
    /- 6.6 -/
    else if c? == some '\u003A'
    then
      /- 6.6.1 -/
      modify fun s => { s with pointer := s.pointer + 1 }
      /- 6.6.2 -/
      if (← curr?).isNone then throw (ipv6InvalidCodePoint, none, none)
    /- 6.7-/
    else if !((← curr?).isNone) then throw (ipv6InvalidCodePoint, none, none)
    modify fun m => {
      m with
      /- 6.8 -/
      address := m.address.set! m.pieceIndex value
      /- 6.9 -/
      pieceIndex := m.pieceIndex + 1
    }
  /- 7. -/
  if let some compress := (← get).compress
  then
    /- 7.1, 7.2 -/
    modify fun s => { s with swaps := s.pieceIndex - compress, pieceIndex := 7 }
    /- 7.3 -/
    while (← get).pieceIndex != 0 && (← get).swaps > 0 do
      let lhsIdx := (← get).pieceIndex
      -- Doesn't need signed integers because `swaps` > 0
      let rhsIdx := compress + ((← get).swaps - 1)
      --
      if (← get).address.size ≤ (max lhsIdx rhsIdx) then panic! "bad swap in ipv6"
      modify fun s => {
        s with
        address := s.address.swapIfInBounds lhsIdx rhsIdx
        pieceIndex := s.pieceIndex - 1
        swaps := s.swaps - 1
      }
  /- 8. -/
  else
    if (← get).pieceIndex != 8
    then
      let dbg := (← get).pieceIndex
      throw (ipv6TooFewPieces, some (Int.ofNat (← get).pointer), some s!"{dbg}, {sourceLoc!}")
  /- 9. -/
  return

def parse (input : Array Char) : Except SyntaxViolationLog (Vector UInt16 8) :=
  let st:= {
    pieceIndex := 0
    compress := none
    numbersSeen := 0
    address : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]
    input
    pointer := 0
    swaps := 0
  }
  match parse'.run st with
  | .ok _ s =>
    let mapped := s.address.filterMap (fun x =>
      if x < UInt16.size
      then some (UInt16.ofNat x)
      else none
    )
    if h : mapped.size = 8
    then .ok (h ▸ (mapped.toVector))
    else .error (SyntaxViolation.ipv4InIpv6OutOfRange, none, none)
  | .error e _ => .error e
