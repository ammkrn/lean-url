import LeanUrl.Util
import LeanUrl.Parser.Util
import LeanUrl.Parser.Ipv4Number
import LeanUrl.Url.Basic

import Std.Net

namespace LeanUrl.Parser.Ipv4

structure State where
  address : Array Char
  input : Array Char
  pointer : Nat
  parts : List String
  errorLog : Array SyntaxViolationLog
deriving Inhabited

open SyntaxViolation

def parseAux : EStateM SyntaxViolationLog State Nat := do
  let mut parts := (strictSplit (← get).input '.').map (fun s => s.toList.toArray)
  if let some #[] := parts.back?
  then
    modify fun s => { s with errorLog := s.errorLog.push (ipv4EmptyPart, none, some sourceLoc!)}
    /- 2.1 -/
    if parts.size > 1
    /- 2.2 -/
    then parts := parts.pop
  /- 3. -/
  if parts.size > 4 then throw (ipv4TooManyParts, none, some sourceLoc!)
  /- 4. -/
  let mut numbers : Array Nat := #[]

  for part in parts do
    /- 5.1, 5.2 -/
    let (a, b) ← Ipv4Number.parse part
    /- 5.2 -/
    /- 5.3 -/
    if b then modify fun st => { st with errorLog := st.errorLog.push (ipv4NonDecimalPart, none, some sourceLoc!)}
    numbers := numbers.push a
  /- 5.4 -/
  for (number, idx) in numbers.zipIdx do
    if number > 255
    then
      modify fun st => { st with errorLog := st.errorLog.push (ipv4OutOfRange, none, some sourceLoc!) }
      if idx + 1 < numbers.size
      then
        throw (ipv4OutOfRange, none, some sourceLoc!)
      else
        if number ≥ (256 ^ (5 - numbers.size))
        then
          throw (ipv4OutOfRange, none, some sourceLoc!)
  let mut ipv4 := numbers.back!
  numbers := numbers.pop
  let mut counter := 0
  for n in numbers do
    ipv4 := ipv4 + (n * (256 ^ (3 - counter)))
    counter := counter + 1
  return ipv4

def parseUInt32 (s : String) : Except SyntaxViolationLog UInt32 :=
  match parseAux.run { input := s.toArray, pointer := 0, address := #[], parts := [], errorLog := #[] } with
  | .ok a _ =>
    if a < UInt32.size
    then .ok (UInt32.ofNat a)
    else .error (SyntaxViolation.ipv4OutOfRange, none, none)
  | .error e _ => .error e

def parse (s : String) : Except SyntaxViolationLog Std.Net.IPv4Addr :=
  match parseAux.run { input := s.toArray, pointer := 0, address := #[], parts := [], errorLog := #[] } with
  | .ok a _ =>
    if a < UInt32.size
    then
      match Std.Net.IPv4Addr.ofString (serializeIpv4 a) with
      | some out => .ok out
      | _ => .error (SyntaxViolation.ipv4OutOfRange, none, some s!"failed to convert to std ipv4: {sourceLoc!}")
    else .error (SyntaxViolation.ipv4OutOfRange, none, none)
  | .error e _ => .error e
