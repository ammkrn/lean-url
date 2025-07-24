import LeanUrl.Percent.Basic

open Std (HashSet)
open LeanUrl.Percent


/-- info: "%23" -/
#guard_msgs in
#eval percentEncodeByte 0x23

/-- info: "%00" -/
#guard_msgs in
#eval percentEncodeByte 0x00

/-- info: "%7F" -/
#guard_msgs in
#eval percentEncodeByte 0x7F

/-- info: "%80" -/
#guard_msgs in
#eval percentEncodeByte 0x80

/-- info: "%FF" -/
#guard_msgs in
#eval percentEncodeByte 0xFF

-- Test UTF-8 percent encoding
/-- info: "Hello%20World%21" -/
#guard_msgs in
#eval utf8PercentEncode "Hello World!" (HashSet.emptyWithCapacity.insert ' ' |>.insert '!')

/-- info: "%E2%89%A1" -/
#guard_msgs in
#eval utf8PercentEncode "≡" PercentEncodeSets.c0Controls

/-- info: "%E2%80%BD" -/
#guard_msgs in
#eval utf8PercentEncode "‽" PercentEncodeSets.c0Controls

/-- info: [102, 111, 111, 32, 98, 97, 114, 63] -/
#guard_msgs in
#eval percentDecode "foo%20bar%3F".toUTF8

/-- info: [37, 37, 115, 37, 49, 71] -/
#guard_msgs in
#eval percentDecode "%25%s%1G".toUTF8

/-- info: "%%s%1G" -/
#guard_msgs in
#eval
  let input := "%25%s%1G".toUTF8
  let output := percentDecode input
  String.fromUTF8! output

/-- info: "foo bar?" -/
#guard_msgs in
#eval
  let input := "foo%20bar%3F".toUTF8
  let output := percentDecode input
  String.fromUTF8! output

-- Test percent encoding with sets
open PercentEncodeSets

/-- info: "foo%20%3Cbar%3E" -/
#guard_msgs in
#eval utf8PercentEncode "foo <bar>" fragment

/-- info: "foo%20bar%23baz" -/
#guard_msgs in
#eval utf8PercentEncode "foo bar#baz" query

/-- info: "Say%20what%E2%80%BD" -/
#guard_msgs in
#eval utf8PercentEncode "Say what‽" component

/-- info: Except.ok "foo bar" -/
#guard_msgs in
#eval percentEncodeAfterEncoding "UTF-8" "foo bar" PercentEncodeSets.c0Controls

/-- info: Except.ok "foo+bar" -/
#guard_msgs in
#eval percentEncodeAfterEncoding "UTF-8" "foo bar" PercentEncodeSets.c0Controls true

/- Test with fragment encode set which includes space -/
/-- info: Except.ok "foo%20bar" -/
#guard_msgs in
#eval percentEncodeAfterEncoding "UTF-8" "foo bar" PercentEncodeSets.fragment

/-- info: Except.ok "foo%20%3Cbar%3E" -/
#guard_msgs in
#eval percentEncodeAfterEncoding "utf-8" "foo <bar>" PercentEncodeSets.fragment

/- Test with non-ASCII characters -/
/-- info: Except.ok "%E2%89%A1" -/
#guard_msgs in
#eval percentEncodeAfterEncoding "UTF-8" "≡" PercentEncodeSets.c0Controls

/- Test empty string -/
/-- info: Except.ok "" -/
#guard_msgs in
#eval percentEncodeAfterEncoding "UTF-8" "" PercentEncodeSets.c0Controls

-- UTF-8 Decoding Tests

-- Test UTF-8 decode with BOM
/-- info: "Hello" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0xEF, 0xBB, 0xBF, 0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
  utf8Decode bytes

-- Test UTF-8 decode without BOM
/-- info: "World" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0x57, 0x6F, 0x72, 0x6C, 0x64]⟩
  utf8Decode bytes

-- Test UTF-8 decode with invalid sequence (replacement mode)
/-- info: "A�B" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0x41, 0xFF, 0x42]⟩
  utf8DecodeWithoutBOM bytes

-- Test UTF-8 decode without BOM or fail with valid UTF-8
/-- info: some "Test" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0x54, 0x65, 0x73, 0x74]⟩
  utf8DecodeWithoutBOMOrFail? bytes

-- Test UTF-8 decode without BOM or fail with invalid UTF-8
/-- info: none -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0x41, 0xFF, 0x42]⟩
  utf8DecodeWithoutBOMOrFail? bytes

-- Test UTF-8 decode with multi-byte characters
/-- info: "€₹" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0xE2, 0x82, 0xAC, 0xE2, 0x82, 0xB9]⟩
  utf8DecodeWithoutBOM bytes

-- Test empty byte array
/-- info: "" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[]⟩
  utf8Decode bytes

-- Test BOM only
/-- info: "" -/
#guard_msgs in
#eval
  let bytes : ByteArray := ⟨#[0xEF, 0xBB, 0xBF]⟩
  utf8Decode bytes


section WptTests

/-
Tests from
https://github.com/web-platform-tests/wpt/blob/befe66343e5f21dc464c8c772c6d20695936714f/url/resources/percent-encoding.json
-/

/-- info: "%C3%A1|" -/
#guard_msgs in
#eval
  let input := "á|"
  utf8PercentEncode input LeanUrl.Percent.PercentEncodeSets.c0Controls

/-- info: "%E2%80%A0" -/
#guard_msgs in
#eval
  let input := '\u2020'.toString
  utf8PercentEncode input LeanUrl.Percent.PercentEncodeSets.c0Controls

/-- info: "%E2%80%BE\\" -/
#guard_msgs in
#eval
  let input := s!"{'\u203E'}{'\u005C'}"
  utf8PercentEncode input LeanUrl.Percent.PercentEncodeSets.c0Controls

/-- info: "%EE%97%A5" -/
#guard_msgs in
#eval
  let input := '\ue5e5'.toString
  utf8PercentEncode input LeanUrl.Percent.PercentEncodeSets.c0Controls

/-- info: "%E2%88%92" -/
#guard_msgs in
#eval
  let input := '\u2212'.toString
  utf8PercentEncode input LeanUrl.Percent.PercentEncodeSets.c0Controls

/-- info: "%0EA" -/
#guard_msgs in
#eval
  let input := '\u000e'.toString ++ "A"
  utf8PercentEncode input LeanUrl.Percent.PercentEncodeSets.c0Controls

end WptTests

def Nat.toHexString (i : Nat) (leftpad : Nat := 0) : String := Id.run  do
  let rec aux (i : Nat) (acc : List Char) : List Char :=
    if h : i < 16
    then
      Nat.digitChar i :: acc
    else
      let cur := Nat.digitChar (i % 16)
      aux (i / 16) (cur :: acc)
  ((aux i []).leftpad leftpad '0').asString.toUpper

namespace LeanUrl.Percent.Tests.PercentMod
open PercentEncodeSets

-- Test percent_encode_byte for all byte values
/-- info: true -/
#guard_msgs in
#eval
  (List.range 256).all fun i =>
    let encoded := percentEncodeByte (UInt8.ofNat i)
    let expected := s!"%{i.toHexString (leftpad := 2)}"
    encoded == expected

-- Test utf8_percent_encode accepts ascii_set ref
/-- info: true -/
#guard_msgs in
#eval
  let encoded := utf8PercentEncode "foo bar?" HashSet.emptyWithCapacity
  encoded == "foo bar?"

-- Test percent_decode
/-- info: true -/
#guard_msgs in
#eval
  let decoded := percentDecode "foo%20bar%3f".toUTF8
  let result := String.fromUTF8! decoded
  result == "foo bar?"

-- Test percent_decode_str
/-- info: true -/
#guard_msgs in
#eval
  let decoded := percentDecodeStr "foo%20bar%3f"
  let result := String.fromUTF8! decoded
  result == "foo bar?"

-- Test percent_decode collect
/-- info: true -/
#guard_msgs in
#eval
  let decoded := percentDecode "foo%20bar%3f".toUTF8
  decoded == "foo bar?".toUTF8

-- Test percent_decode with no encoding vs with encoding
/-- info: true -/
#guard_msgs in
#eval
  let decoded1 := percentDecode "foo%20bar%3f".toUTF8
  let decoded2 := percentDecode "foo bar?".toUTF8

  -- First should decode the %20 and %3f
  String.fromUTF8! decoded1 == "foo bar?" &&
  -- Second should remain unchanged
  String.fromUTF8! decoded2 == "foo bar?"

-- Test percent_decode UTF-8 lossy
/-- info: true -/
#guard_msgs in
#eval
  -- Valid UTF-8 emoji
  let decoded := percentDecode "%F0%9F%92%96".toUTF8
  let result := String.fromUTF8! decoded
  -- The emoji is 💖 which is U+1F496
  result == "💖"

-- Test percent_decode UTF-8 lossy with invalid UTF-8
-- This would use replacement character in lossy decoding
/-- info: true -/
#guard_msgs in
#eval
  -- Create invalid UTF-8 sequence
  let decoded := percentDecode "%00%9F%92%96".toUTF8
  -- In our implementation, we just decode the bytes
  decoded == ByteArray.mk #[0x00, 0x9F, 0x92, 0x96]

end LeanUrl.Percent.Tests.PercentMod
