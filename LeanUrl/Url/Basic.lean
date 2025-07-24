import LeanUrl.Util
import Std.Net

def String.isSpecialScheme (s : String) : Bool :=
  match s.toLower with
  | "http" | "https" | "ws" | "wss" | "file" | "ftp" => true
  | _ => false

def String.defaultPortForScheme (s : String) : Option UInt16 :=
  match s.toLower with
  | "http" => some 80
  | "https" => some 443
  | "ws" => some 80
  | "wss" => some 443
  | "ftp" => some 21
  | _ => none

namespace LeanUrl

structure Domain where
  val : String
  h : !val.isEmpty
deriving Repr

namespace Domain

def labels (d : Domain) : Array String := strictSplit d.val.toList.toArray '\u002E'

end Domain

def serializeIpv4 (ipv4 : UInt32) : String := Id.run do
  let mut out := ""
  let mut n : UInt32 := ipv4
  for i in [1:5] do
    out := s!"{(n % 256)}" ++ out
    if i != 4 then out := "." ++ out
    n := n / 256
  return out

def printHex : Nat → String
  | 0 => "0"
  | n@(_+1) =>
    let rec aux : Nat → List Char → List Char
      | 0, sink => sink
      | n@(_+1), sink =>
        aux (n / 16) ((Nat.digitChar (n % 16)) :: sink)
    (aux n []).foldl (init := "") (fun sink next => sink.push next)

def ipv6Find (ipv6 : Std.Net.IPv6Addr) : Option Nat := Id.run do
  let mut longestIndex : Option Nat := none
  let mut longestSize := 1
  let mut foundIndex : Option Nat := none
  let mut foundSize := 0
  for (piece, pieceIndex) in ipv6.segments.zipIdx do
    /- 1. -/
    if piece != 0
    then
      if foundSize > longestSize
      then
        longestIndex := foundIndex
        longestSize := foundSize
      foundIndex := none
      foundSize := 0
    else
      if foundIndex.isNone then foundIndex := some pieceIndex
      foundSize := foundSize + 1
  if foundSize > longestSize then return foundIndex
  return longestIndex

def serializeIpv6 (ipv6 : Std.Net.IPv6Addr) : String := Id.run do
  let mut out := ""
  let compress := ipv6Find ipv6
  let mut ignore0 := false
  for (piece, pieceIndex) in ipv6.segments.zipIdx do
    /- 1. -/
    if ignore0 && piece == 0 then continue
    /- 2. -/
    else if ignore0 then ignore0 := false
    /- 3. -/
    if compress = some pieceIndex
    then
      /- 3.1 -/
      let separator := if pieceIndex == 0 then "::" else ":"
      /- 3.2 -/
      out := out.append separator
      /- 3.3 -/
      ignore0 := true
      continue
    /- 4. -/
    out := out.append (printHex piece.toNat)
    /- 5. -/
    if pieceIndex != 7 then out := out.push '\u003A'
  return out

/-- An opaque host is a non-empty ASCII string that can be used for further processing. -/
structure OpaqueHost where
  val : String
  h : !val.isEmpty
deriving Repr


instance : Repr Std.Net.IPv4Addr where
  reprPrec a _ := a.toString

instance : Repr Std.Net.IPAddr where
  reprPrec a _ :=
    match a with
    | .v4 x => x.toString
    | .v6 addr => serializeIpv6 addr

/- 3.1 Host representation -/
inductive Host
  | domain : Domain → Host
  | ipAddr : Std.Net.IPAddr → Host
  | opq : OpaqueHost → Host
  -- An empty host is the empty string.
  | empty : Host
deriving Repr


namespace Host

def isLocalhost : Host → Bool
  | .domain ⟨s, _⟩ | .opq ⟨s, _⟩ => s == "localhost"
  | _ => false

/-
The host serializer takes a host host and then runs these steps. They return an ASCII string.
    If host is an IPv4 address, return the result of running the IPv4 serializer on host.
    Otherwise, if host is an IPv6 address, return U+005B ([), followed by the result of running the IPv6 serializer on host, followed by U+005D (]).
    Otherwise, host is a domain, opaque host, or empty host, return host.
-/
def serialize : Host → String
  | .ipAddr (.v4 x) => x.toString
  | .ipAddr (.v6 addr) => "[" ++ serializeIpv6 addr ++ "]"
  | .domain d => d.val
  | .opq o => o.val
  /- The spec says ".empty = empty string"-/
  | .empty => ""


def publicSuffixListAlgo (s : String): String := sorry
/-
To obtain the public suffix of a host host, run these steps. They return null or a domain representing a portion of host that is included on the Public Suffix List. [PSL]
    If host is not a domain, then return null.
    Let trailingDot be "." if host ends with "."; otherwise the empty string.
    Let publicSuffix be the public suffix determined by running the Public Suffix List algorithm with host as domain. [PSL]
    Assert: publicSuffix is an ASCII string that does not end with ".".
    Return publicSuffix and trailingDot concatenated.
-/
def publicSuffix : Host → Option String
  | .domain ⟨s, _⟩ =>
    let trailingDot := if s.endsWith "." then "." else ""
    let publicSuffix : String := publicSuffixListAlgo s
    assert! (publicSuffix.all (fun c => c.toNat ≤ 255)) && !(publicSuffix.endsWith ".")
    some (publicSuffix ++ trailingDot)
  | _ => none

/-
Examples:
  com 	com 	null
  example.com 	com 	example.com
  www.example.com 	com 	example.com
  sub.www.example.com 	com 	example.com
  EXAMPLE.COM 	com 	example.com
  example.com. 	com. 	example.com.
  github.io 	github.io 	null
  whatwg.github.io 	github.io 	whatwg.github.io
  إختبار 	xn--kgbechtv 	null
  example.إختبار 	xn--kgbechtv 	example.xn--kgbechtv
  sub.example.إختبار 	xn--kgbechtv 	example.xn--kgbechtv
  [2001:0db8:85a3:0000:0000:8a2e:0370:7334] 	null 	null

To obtain the registrable domain of a host host, run these steps. They return null or a domain formed by host’s public suffix and the domain label preceding it, if any.
    If host’s public suffix is null or host’s public suffix equals host, then return null.
    Let trailingDot be "." if host ends with "."; otherwise the empty string.
    Let registrableDomain be the registrable domain determined by running the Public Suffix List algorithm with host as domain. [PSL]
    Assert: registrableDomain is an ASCII string that does not end with ".".
    Return registrableDomain and trailingDot concatenated.
-/
def registrableDomain (h : Host) : Option String :=
  match h.publicSuffix with
  | none => none
  | some h' => sorry
end Host

/- 4.1 -/
structure Url where
  scheme       : String
  username     : Option String
  password     : Option String
  host         : Option Host
  port         : Option UInt16
  path         : Sum String (Array String)
  query        : Option String
  fragment     : Option String
  blobUrlEntry : Option String
deriving Repr

/- 4.1 -/
instance : Inhabited Url where
  default := {
    scheme := ""
    username := none
    password := none
    host := none
    port := none
    path := .inr #[]
    query := none
    fragment := none
    blobUrlEntry := none
  }

namespace Url

def schemeIsSpecial (url : Url) : Bool := url.scheme.isSpecialScheme

def hasCredentials (url : Url) : Bool :=
  let isNonempty : Option String → Bool
    | none => false
    | some x => !x.isEmpty
  isNonempty url.username || isNonempty url.password


structure Origin where
  val : Option String

/-
4.7

Opaque origin is `none`, serialized as `null` (?)
-/
def origin (url : Url) : Origin :=
  if let some blob := url.blobUrlEntry
  then
    sorry
  else
    sorry

namespace Origin
end Origin

def protocol (url : Url) : String := sorry

def hostname (url : Url) : String := sorry

def pathname (url : Url) : String := sorry

/-
If url’s query is non-null, append U+003F (?), followed by url’s query, to output.
-/
def search (url : Url) : String :=
  match url.query with
  | none | some "" => ""
  | some q => s!"?{q}"

def hash (url : Url) (excludeFragment : Bool) : String :=
  match excludeFragment, url.fragment with
  | _, none | _, some "" | true, _ => ""
  | false, some fragment => s!"#{fragment}"

def opaquePath (url : Url) : Bool :=
  match url.path with
  | .inl _ => true
  | .inr _ => false

def isSpecial (url : Url) : Bool := url.scheme.isSpecialScheme

def isFile (url : Url) : Bool := url.scheme.toLower == "file"

def pathSize (url : Url) : Nat :=
  match url.path with
  | .inl _ => 1
  | .inr xs => xs.size

def isDefaultPortForScheme' (url : Url) (port : UInt16) : Bool :=
  match url.scheme.defaultPortForScheme with
  | none => false
  | some p => p == port


def isWsOrWss (url : Url) : Bool :=
  match url.scheme.toLower with
  | "ws" | "wss" => true
  | _ => false

def rule_4_1_Ck (url : Url) : Except String Unit :=
  match url.isSpecial, url.path with
  | true, .inl _ => .error "A special URL’s path is always a list, i.e., it is never opaque."
  | _, _ => .ok ()

def rule_4_2_Ck (url : Url) : Except String Unit :=
  if (url.host.isNone || url.host matches (some .empty) || url.isFile) && (url.hasCredentials || url.port.isSome)
  then
    .error "A URL cannot have a username/password/port if its host is null or the empty string, or its scheme is 'file'."
  else
    .ok ()

def pathIsEmpty (url : Url) : Bool :=
  match url.path with
  | .inl "" => true
  | .inr #[] => true
  | _ => false

def pathPfx (url : Url) : Option String :=
  match url.path with
  | .inl x => some x
  | .inr xs => xs[0]?

def serializePath (url : Url) : String := Id.run do
  match url.path with
  | .inl p => return p
  | .inr segments =>
    let mut out := ""
    for segment in segments do
      out := out.append s!"/{segment}"
    return out

/-
4.5 URL serializing
-/
def serialize (url : Url) (excludeFragment : Bool) : String := Id.run do
  /- 1. -/
  let mut out := s!"{url.scheme}:"
  /- 2. -/
  if let some host := url.host
  then
    /- 2.1 -/
    out := out ++ "//"
    /- 2.2 -/
    if url.hasCredentials
    then
      -- Assumes that you will never have JUST the password.
      /- 2.2.1 -/
      if url.username.isSome then out := out.append url.username.get!
      --out := out.append url.username.get!
      /- 2.2.2 -/
      if url.password.isSome && url.password != some ""
      then
        out := out.push '\u003A'
        out := out.append url.password.get!
      /- 2.2.3 -/
      out := out.push '@'
    /- 2.3 -/
    out := out.append host.serialize
    /- 2.4 -/
    if !url.port.isNone
    then
      out := out.push '\u003A'
      out := out.append s!"{url.port.get!}"
  /- 3. -/
  if url.host.isNone && !url.opaquePath && url.pathSize > 1 && url.pathPfx == some ""
  then
    out := (out.push '\u002F').push '\u002E'
  /- 4.-/
  out := out.append url.serializePath
  /- 5. -/
  if !url.query.isNone
  then
    out := out ++ "?" ++ url.query.get!
  /- 6. -/
  if !excludeFragment && !url.fragment.isNone
  then
    out := out ++ "#" ++ url.fragment.get!
  /- 7. -/
  return out

/- 4.6. URL equivalence -/
def equiv (a b : Url) (excludeFragment : Bool) : Bool :=
  (a.serialize excludeFragment) == (b.serialize excludeFragment)
