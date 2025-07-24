import LeanUrl.Util
import Std.Data.HashSet

open Std (HashSet)
open String (validateUTF8 fromUTF8? utf8DecodeChar?)

namespace LeanUrl.Percent

def hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (c.toNat - 'a'.toNat + 10)
  else
    none

/- WHATWG percent-encode sets -/
namespace PercentEncodeSets

/-- C0 controls are 0x00-0x1F and 0x7F
  The C0 control percent-encode set are the C0 controls and all code points
  greater than U+007E (~).
-/
def c0Controls : HashSet Char :=
  (List.range 0x20).foldl
    (init := HashSet.emptyWithCapacity)
    (fun acc n => acc.insert (Char.ofNat n))
  |>.insert (Char.ofNat 0x7F)

/--
The fragment percent-encode set is the C0 control percent-encode set and
U+0020 SPACE, U+0022 ("), U+003C (<), U+003E (>), and U+0060 (`).
-/
def fragment : HashSet Char :=
  c0Controls
    |>.insert ' '
    |>.insert '"'
    |>.insert '<'
    |>.insert '>'
    |>.insert '`'

/--
The query percent-encode set is the C0 control percent-encode set and
U+0020 SPACE, U+0022 ("), U+0023 (#), U+003C (<), and U+003E (>).
-/
def query : HashSet Char :=
  c0Controls
    |>.insert ' '
    |>.insert '"'
    |>.insert '#'
    |>.insert '<'
    |>.insert '>'

/--
The special-query percent-encode set is the query percent-encode set and U+0027 (').
-/
def specialQuery : HashSet Char :=
  query.insert '\''

/--
The path percent-encode set is the query percent-encode set and U+003F (?),
U+005E (^), U+0060 (`), U+007B ({), and U+007D (}).
-/
def path : HashSet Char :=
  query
    |>.insert '?'
    |>.insert '^'
    |>.insert '`'
    |>.insert '{'
    |>.insert '}'

/--
The userinfo percent-encode set is the path percent-encode set and U+002F (/),
U+003A (:), U+003B (;), U+003D (=), U+0040 (@), U+005B ([) to U+005D (]),
inclusive, and U+007C (|).
-/
def userinfo : HashSet Char :=
  path
    |>.insert '/'
    |>.insert ':'
    |>.insert ';'
    |>.insert '='
    |>.insert '@'
    |>.insert '['
    |>.insert '\\'
    |>.insert ']'
    |>.insert '|'

/--
The component percent-encode set is the userinfo percent-encode set and
U+0024 ($) to U+0026 (&), inclusive, U+002B (+), and U+002C (,).
-/
def component : HashSet Char :=
  userinfo
    |>.insert '$'
    |>.insert '%'
    |>.insert '&'
    |>.insert '+'
    |>.insert ','

/--
The application/x-www-form-urlencoded percent-encode set is the component
percent-encode set and U+0021 (!), U+0027 (') to U+0029 RIGHT PARENTHESIS,
inclusive, and U+007E (~).

The application/x-www-form-urlencoded percent-encode set contains all code points,
except the ASCII alphanumeric, U+002A (*), U+002D (-), U+002E (.), and U+005F (_).
-/
def formUrlEncoded : HashSet Char :=
  (List.range 128).foldl
    (init := HashSet.emptyWithCapacity)
    fun acc n =>
      let c := Char.ofNat n
      if c.isAlphanum || c = '*' || c = '-' || c = '.' || c = '_'
      then acc
      else acc.insert c

end PercentEncodeSets

/--
To percent-encode a byte `byte`, return a string consisting of U+0025 (%),
followed by two ASCII upper hex digits representing `byte`.
(WHATWG spec: "To percent-encode a byte")
-/
def percentEncodeByte (byte : UInt8) : String :=
  let high := byte.toNat / 16
  let low := byte.toNat % 16
  let highChar := if high < 10 then Char.ofNat ('0'.toNat + high) else Char.ofNat ('A'.toNat + high - 10)
  let lowChar := if low < 10 then Char.ofNat ('0'.toNat + low) else Char.ofNat ('A'.toNat + low - 10)
  "%" |>.push highChar |>.push lowChar

def percentDecode (input : ByteArray) : ByteArray :=
  let rec aux (pos : Nat) (output : ByteArray) : ByteArray :=
    if h : pos < input.size then
      let byte := input[pos]
      if byte != 0x25
      then
        /- 1. -/
        aux (pos + 1) (output.push byte)
      else
        /- 2 -/
        let c1 := input[pos + 1]?.map Char.ofUInt8
        let c2 := input[pos + 2]?.map Char.ofUInt8
        match c1.bind hexDigitToNat?, c2.bind hexDigitToNat? with
        | some h, some l =>
          /- 2.3 -/
          let decodedByte := UInt8.ofNat (h * 16 + l)
          aux (pos + 3) (output.push decodedByte)
        | _, _ =>
          /- 2.2. -/
          aux (pos + 1) (output.push byte)
    else
      output
  aux 0 ByteArray.empty

def percentDecodeStr (input : String) : ByteArray :=
  percentDecode input.toUTF8

/--
percent-encoded-byte 1.3
-/
def percentEncodeAfterEncoding_ (encoding : String) (input : String) (percentEncodeSet : HashSet Char) (spaceAsPlus : Bool := false) : Except String String :=
  if !(encoding.toLower = "utf-8" || encoding.toLower = "utf8")
  then .error "non-utf8 encodings not yet supported"
  else Id.run do
    let inputQueue := input.toUTF8
    let mut output := ""
    let mut potentialError := some 0
    while potentialError.isSome do
      /- since we're not yet supporting alternative encodings. -/
      let encodeOutput := inputQueue
      for byte in encodeOutput do
        if spaceAsPlus && byte == 0x20
        then
          output := output.push '\u002B'
          continue
        /- 5.3.2 -/
        let isomorph := Char.ofUInt8 byte
        /- 5.3.3, 5.3.4; if it's non-ascii or it's ascii and in the encode set, then encode it -/
        if (!isomorph.isAscii || percentEncodeSet.contains isomorph)
        then output := (output ++ percentEncodeByte byte)
        /- 5.3.5 -/
        else output := output.push isomorph
        if potentialError.isSome
        then sorry
    .ok output

/--
Temporary implementation for utf8 only since we don't yet support alternate encodings.
-/
def percentEncodeAfterEncoding (encoding : String) (input : String) (percentEncodeSet : HashSet Char) (spaceAsPlus : Bool := false) : Except String String :=
  if encoding.toLower = "utf-8" || encoding.toLower = "utf8" then
    let bytes := input.toUTF8
    /- For each byte -/
    let rec percentEncodeBytes (pos : Nat) (acc : String) : String :=
      if h : pos < bytes.size then
        let byte := bytes[pos]
        /- 5.3.1 -/
        if spaceAsPlus && byte = 0x20 then
          percentEncodeBytes (pos + 1) (acc ++ "+")
        else
          /- 5.3.2 -/
          let isomorph := Char.ofUInt8 byte
          /- 5.3.3, 5.3.4; if it's non-ascii or it's ascii and in the encode set, then encode it -/
          if !isomorph.isAscii || percentEncodeSet.contains isomorph then
            percentEncodeBytes (pos + 1) (acc ++ percentEncodeByte byte)
          else
            /- 5.3.5 -/
            percentEncodeBytes (pos + 1) (acc ++ String.singleton isomorph)
      else
        acc

    .ok (percentEncodeBytes 0 "")
  else
    .error s!"unsupported encoding {encoding}"

/--
"To UTF-8 percent-encode a scalar value string `input` using a `percentEncodeSet`,
return the result of running percent-encode after encoding with UTF-8, `input`,
and `percentEncodeSet`."
-/
def utf8PercentEncode (input : String) (encodeSet : HashSet Char) : String :=
  match percentEncodeAfterEncoding "UTF-8" input encodeSet false with
  | .ok result => result
  | .error _ => panic! s!"encoding should not fail for utf-8"

/- decoding -/

/--
Process a ByteArray with a UTF-8 decoder.
whatwg spec calls this "process a queue" with utf-8 decoder.

When `errorMode` is "replacement", invalid UTF-8 sequences are replaced with U+FFFD.
When `errorMode` is "fatal", returns `none` if invalid UTF-8 is encountered.
-/
def processQueueWithUTF8Decoder (bytes : ByteArray) (errorMode : String) : Option String := do
  if errorMode = "fatal" then
    if validateUTF8 bytes then
      fromUTF8? bytes
    else
      none
  else
    /- Replacement mode: decode with replacement characters -/
    let mut result := ""
    let mut i := 0
    while i < bytes.size do
      match utf8DecodeChar? bytes i with
      | some c =>
        result := result.push c
        i := i + c.utf8Size
      | none =>
        /- Invalid UTF-8 sequence, use replacement character
           U+FFFD REPLACEMENT CHARACTER -/
        result := result.push '\uFFFD'
        i := i + 1
    some result

/--
To UTF-8 decode an I/O queue of bytes `ioQueue` given an optional I/O queue of scalar values
`output` (default « »), run these steps:

1. Let buffer be the result of peeking three bytes from ioQueue, converted to a byte sequence.
2. If buffer is 0xEF 0xBB 0xBF, then read three bytes from ioQueue. (Do nothing with those bytes.)
3. Process a queue with an instance of UTF-8's decoder, ioQueue, output, and "replacement".
4. Return output.

(WHATWG spec: "To UTF-8 decode")
-/
def utf8Decode (bytes : ByteArray) : String :=
  /- Check for BOM (0xEF 0xBB 0xBF) -/
  let bytesAfterBOM :=
    if bytes.size >= 3 &&
       bytes[0]! = 0xEF &&
       bytes[1]! = 0xBB &&
       bytes[2]! = 0xBF then
      bytes.extract 3 bytes.size
    else
      bytes
  /- Process with replacement mode -/
  match processQueueWithUTF8Decoder bytesAfterBOM "replacement" with
  | some result => result
  | none => panic! "should not fail"

/--
To UTF-8 decode without BOM an I/O queue of bytes `ioQueue` given an optional I/O queue of
scalar values `output` (default « »), run these steps:

1. Process a queue with an instance of UTF-8's decoder, ioQueue, output, and "replacement".
2. Return output.

(WHATWG spec: "To UTF-8 decode without BOM")
-/
def utf8DecodeWithoutBOM (bytes : ByteArray) : String :=
  match processQueueWithUTF8Decoder bytes "replacement" with
  | some result => result
  | none => panic! "should not fail"

/--
To UTF-8 decode without BOM or fail an I/O queue of bytes `ioQueue` given an optional I/O queue
of scalar values `output` (default « »), run these steps:

1. Let potentialError be the result of processing a queue with an instance of UTF-8's decoder,
   ioQueue, output, and "fatal".
2. If potentialError is an error, then return failure.
3. Return output.

(WHATWG spec: "To UTF-8 decode without BOM or fail")
-/
def utf8DecodeWithoutBOMOrFail? (bytes : ByteArray) : Option String :=
  processQueueWithUTF8Decoder bytes "fatal"
