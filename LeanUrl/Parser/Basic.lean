import LeanUrl.Util
import LeanUrl.Parser.Util
import LeanUrl.Url.Basic
import LeanUrl.Percent.Basic
import LeanUrl.Parser.Host

open LeanUrl.Percent

namespace LeanUrl.Parser

/-
The way they wrote the state machine is strange and sort of precludes
direct use of an iterator.

+ The counter increment happens at the end of the loop;;

+ They assume a signed integer type is being used as the pointer, such
that failure in e.g. schemeStart can roll back to -1 so that
the return to the main loop can bump to 0 and start over.

+ They assume that states will be able to see the s[i] = EOF state
and can act on it.

Naively trying to adapt the spec to a Nat-based iterator run into trouble because
some of the steps expect to get in a last word when the iterator is exhausted.
-/
inductive State
  | schemeStart
  | scheme
  | noScheme
  | specialRelativeOrAuthority
  | pathOrAuthority
  | relative
  | relativeSlash
  | specialAuthoritySlashes
  | specialAuthorityIgnoreSlashes
  | authority
  | host
  | hostName
  | port
  | file
  | fileSlash
  | fileHost
  | pathStart
  | path
  | opaquePath
  | query
  | fragment
deriving BEq, Repr, Inhabited

open State

structure Machine where
  base : Option Url
  url : Url
  atSignSeen        : Bool := false
  insideBrackets    : Bool := false
  passwordTokenSeen : Bool := false
  buffer            : String := ""
  input             : Array Char
  pointer           : Int
  errorLog          : Array SyntaxViolationLog := #[]
  state             : State := schemeStart
  stateOverride     : Option State := none
deriving Inhabited, Repr

abbrev M := EStateM String Machine

structure Methods where
  encoding : Option String := "utf-8"
  queryEncodingOverride : Option (String → String)
deriving Inhabited

abbrev ParserM := ReaderT Parser.Methods (EStateM String Machine)

def ParserM.run {α : Type} (f : ParserM α) (methods : Methods) (s : Machine)  : EStateM.Result String Machine α :=
  (f methods).run s

def trimTabNewlineCarriageReturn (input : String) : (String × Option SyntaxViolationLog) :=
  let output := input.toList.filter (fun c => !Char.tabOrNewline c) |>.asString
  let v := if input.any Char.tabOrNewline then
    some (.tabOrNewlineIgnored, none, some sourceLoc!)
  else
    none
  (output, v)

def trimc0ControlSpace (input : String) : (String × Option SyntaxViolationLog) :=
  let output := (input.dropWhile Char.c0ControlOrSpace).dropRightWhile Char.c0ControlOrSpace
  let v := if output.length < input.length
    then
      some (.c0SpaceIgnored, none, some sourceLoc!)
    else if output.any Char.tabOrNewline
    then
      some (.tabOrNewlineIgnored, none, some sourceLoc!)
    else none
  (output, v)

def appendPath (toAppend : String) : ParserM Unit := fun _ s =>
  match s.url.path with
  | .inl p => .ok () { s with url := { s.url with path := .inl s!"{p}{toAppend}" }}
  | .inr xs => .ok () {
    s with
    url := {
      s.url with
      path := .inr <| xs.push toAppend
    }
  }

def appendQuery (toAppend : String) : ParserM Unit := fun _ s =>
  .ok () { s with url := {
    s.url with query :=
      match s.url.query with
      | none | some "" => toAppend
      | some owise => s!"{owise}&{toAppend}"
  }}

def appendFragment (toAppend : String) : ParserM Unit := fun _ s =>
  .ok () { s with url := {
    s.url with fragment :=
      match s.url.fragment with
      | none | some "" => toAppend
      | some owise => s!"{owise}{toAppend}"
  }}

def curr? : ParserM (Option Char) := fun _ s =>
  match s.pointer with
  | .ofNat n => .ok s.input[n]? s
  | _ =>  .ok none s

def peekNext1 : ParserM (Option Char) := fun _ s =>
  match s.pointer with
  | .ofNat n => .ok s.input[n+1]? s
  | _ =>  .ok none s

def peekNext2 : ParserM (Option Char) := fun _ s =>
  match s.pointer with
  | .ofNat n => .ok s.input[n+2]? s
  | _ =>  .ok none s

def remaining : ParserM (Option String) := fun _ s =>
  match s.pointer with
  | .ofNat n => .ok (some <| (s.input.drop n).toString) s
  | _ =>  .ok none s

def remainingAfterCurr : ParserM String := fun _ s =>
  match s.pointer with
  | .ofNat n => .ok (s.input.drop (n+1)).toString s
  | _ =>  .ok "" s

def schemeStartState : ParserM Unit := do
  let c? ← curr?
  if (c?.map Char.isAlpha).getD false
  then
    /- 1. -/
    modify (fun m => { m with buffer := m.buffer.push c?.get!.toLower, state := .scheme })
  else if let none := (← get).stateOverride
  then
    /- 2. -/
    modify (fun m => { m with state := .noScheme, pointer := m.pointer - 1 })
  else
    throw sourceLoc!

def schemeState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if (c?.map (·.isAlphanum)).getD false || c? == some '\u002B' || c? == some '\u002D' || c? == some '\u002E'
  then
    modify fun m => { m with buffer := m.buffer.push c?.get!.toLower }
    return
  /- 2. -/
  else if c? == some '\u003A'
  then
    /- 2.1 -/
    if (← get).stateOverride.isSome
    then
      let urlSchemeSpecial := (← get).url.schemeIsSpecial
      let bufferSchemeSpecial := (← get).buffer.isSpecialScheme
      /- 2.1.1 -/
      if urlSchemeSpecial && !bufferSchemeSpecial
      then
        return
      /- 2.1.2 -/
      else if !urlSchemeSpecial && bufferSchemeSpecial
      then
        return
      /- 2.1.3 -/
      else if ((← get).url.hasCredentials || (← get).url.port.isSome) && (← get).buffer == "file"
      then
        return
      /- 2.1.4 -/
      else if (← get).url.isFile && ((← get).url.host.isNone || (← get).url.host matches some .empty)
      then
        return
    /- 2.2 -/
    modify fun m => { m with url := { m.url with scheme := m.buffer }}
    /- 2.3 -/
    if (← get).stateOverride.isSome then
      if some (← get).url.scheme.defaultPortForScheme == (← get).url.port
      then modify fun m => { m with url := { m.url with port := none }}
      return
    /- 2.4 -/
    modify fun m => { m with buffer := "" }
    /- 2.5 -/
    if ((← get).url.isFile)
    then
      if !((← remainingAfterCurr).startsWith "//")
      then modify fun m => { m with errorLog := m.errorLog.push (.specialSchemeMissingFollowingSolidus, m.pointer, some sourceLoc!) }
      modify fun m => { m with state := .file }
    /- 2.6 -/
    else if (← get).url.isSpecial &&
        (← get).base.isSome &&
        (← get).base.get!.scheme == (← get).url.scheme
    then
      if !(((← get).base.map Url.schemeIsSpecial).getD false) then throw s!"assertion failed: base should be special at {sourceLoc!}"
      modify fun m => { m with state := specialRelativeOrAuthority }
    /- 2.7 -/
    else if (← get).url.scheme.isSpecialScheme
    then
      modify fun m => { m with state := specialAuthoritySlashes }
    /- 2.8 -/
    else if (← peekNext1) == some '\u002F'
    then
      modify fun m => { m with state := pathOrAuthority, pointer := m.pointer + 1 }
    /- 2.9 -/
    else
      modify fun m => { m with state := opaquePath, url := { m.url with path := .inl "" } }
    return
  else if let none := (← get).stateOverride
  then
  /- 3. -/
    modify fun m => {
      m with
      buffer := ""
      state := noScheme
      pointer := -1
    }
    return
  /- 4. -/
  else
    throw sourceLoc!

def noSchemeState : ParserM Unit := do
  let c? ← curr?
  let basePathIsOpaque : Bool := ((← get).base.map Url.opaquePath).getD false
  let baseSchemeIsFile : Option Bool :=
    (← get).base.map (fun base => base.isFile)
  /- 1. -/
  if (← get).base.isNone || (basePathIsOpaque && c? != some '\u0023')
  then
    modify fun m => {
      m with
      errorLog := m.errorLog.push (.missingSchemeNonRelativeURL, m.pointer, some sourceLoc!)
    }
    throw sourceLoc!
  /- 2. -/
  else if basePathIsOpaque && c? == some '\u0023'
  then
    modify fun m => {
      m with
      state := fragment
      url := {
        m.url with
        scheme := m.base.get!.scheme
        path := m.base.get!.path
        query := m.base.get!.query
        fragment := ""
      }
    }

  else if !(baseSchemeIsFile.getD false)
  /- 3. -/
  then modify fun m => { m with state := relative, pointer := m.pointer - 1 }
  /- 4. -/
  else modify fun m => { m with state := file, pointer := m.pointer - 1 }


def specialRelativeOrAuthorityState : ParserM Unit := do
  let c? ← curr?
  if c? == some '\u002F' && (← peekNext1) == some '\u002F'
  then
    modify fun m => { m with state := specialAuthorityIgnoreSlashes, pointer := m.pointer + 1 }
  else
    /- 2. -/
    modify fun m => {
      m with
      errorLog := m.errorLog.push (.specialSchemeMissingFollowingSolidus, some m.pointer, some sourceLoc!)
      state := relative
      pointer := m.pointer - 1
    }

def pathOrAuthorityState : ParserM Unit := do
  let c? ← curr?
  if c? == some '\u002F'
  then
    modify fun m => { m with state := authority }
  else
    modify fun m => { m with state := path, pointer := m.pointer - 1 }

def relativeSlashState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if (← get).url.isSpecial && (c? == some '\u002F' || c?== some '\u005C')
  then
    if c? == some '\u005C'
    then modify fun m => { m with errorLog := m.errorLog.push (.invalidReverseSolidus, m.pointer, some sourceLoc!)}
    modify fun m => { m with state := specialAuthorityIgnoreSlashes }
  /- 2. -/
  else if c? == some '\u002F'
  then
    modify fun m => { m with state := authority }
  /- 3. -/
  else if let some base := (← get).base
  then
    modify fun m => {
      m with
      url := {
        m.url with
        username := base.username
        password := base.password
        host := base.host
        port := base.port
      }
      state := path
      pointer := m.pointer - 1
    }
  else
    throw s!"must have base: {sourceLoc!}"

def hostState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if (← get).stateOverride.isSome && ((← get).url.isFile)
  then
    modify fun m => { m with state := fileHost, pointer := m.pointer - 1 }
    return
  /- 2. -/
  else if c? == some '\u003A' && !(← get).insideBrackets
  then
    /- 2.1. -/
    if (← get).buffer == "" then throw sourceLoc!
    /- 2.2. -/
    if (← get).stateOverride == some hostName then throw sourceLoc!
    /- 2.3., 2.4. -/
    let host : Host ←
      match LeanUrl.Parser.Host.parseWwg (← get).buffer.toArray (!(← get).url.isSpecial) with
      | .ok a => pure a
      | .error (_e, _, _) => throw sourceLoc!
    /- 2.5 -/
    modify fun m => {
      m with
      buffer := ""
      state := port
      url := {
        m.url with
        host := host
      }
    }
  /- 3. -/
  else if c?.isNone || c? == some '\u002F' || c? == some '\u003F' || c? == some '\u0023' || ((← get).url.isSpecial && c? == some '\u005C')
  then
    modify fun m => { m with pointer := m.pointer - 1 }
    /- 3.1 -/
    if (← get).url.isSpecial && (← get).buffer == ""
    then
      modify fun m => { m with errorLog := m.errorLog.push (.hostMissing, m.pointer, some sourceLoc!)}
      throw sourceLoc!
    else if
      (← get).stateOverride.isSome &&
      (← get).buffer.isEmpty &&
      ((← get).url.hasCredentials || (← get).url.port.isSome)
    then
      throw sourceLoc!
    else
      let host : Host ←
        match LeanUrl.Parser.Host.parseWwg (← get).buffer.toArray (!(← get).url.isSpecial) with
        | .ok a => pure a
        | .error (_e, _, _) =>
          throw s!"failed to parse host buffer {reprStr _e} {sourceLoc!}"
      modify fun m => {
        m with
        buffer := ""
        state := pathStart
        url := {
          m.url with
          host := host
        }
      }
      if (← get).stateOverride.isSome then return
  else
    /- 4.1 -/
    if c? == some '\u005B' then modify fun m => { m with insideBrackets := true }
    /- 4.2 -/
    if c? == some '\u005D' then modify fun m => { m with insideBrackets := false }
    /- 4.3 -/
    modify fun m => { m with buffer := m.buffer.push c?.get! }

abbrev hostNameState := hostState

def specialAuthoritySlashesState : ParserM Unit := do
  /- 1. -/
  if ((← remaining).map (fun x => x.startsWith "//")).getD false
  then
    modify fun m => { m with state := specialAuthorityIgnoreSlashes, pointer := m.pointer + 1 }
  /- 2. -/
  else
    modify fun m => {
      m with
      pointer := m.pointer - 1
      state := specialAuthorityIgnoreSlashes
      errorLog := m.errorLog.push (.specialSchemeMissingFollowingSolidus, m.pointer, some sourceLoc!)
    }

def specialAuthorityIgnoreSlashesState : ParserM Unit := do
  let c? ← curr?
  if c? != some '\u002F' && c? != some '\u005C'
  then
    modify fun m => { m with state := authority, pointer := m.pointer - 1 }
  else
    modify fun m => {
      m with errorLog := m.errorLog.push (.specialSchemeMissingFollowingSolidus, m.pointer, some sourceLoc!)
    }

def authorityState : ParserM Unit := do
  let c? ← curr?
  if c? == '\u0040'
  then
    /- 1.1 -/
    modify fun m => { m with errorLog := m.errorLog.push (.invalidCredentials, m.pointer, some sourceLoc!)}
    /- 1.2 -/
    if (← get).atSignSeen then modify fun m => { m with buffer := s!"%40{m.buffer}" }
    /- 1.3 -/
    modify fun m => { m with atSignSeen := true }
    /- 1.4 -/
    for c in (← get).buffer.toArray do
      /- 1.4.1 -/
      if c == '\u003A' && !(← get).passwordTokenSeen
      then
        modify fun m => { m with passwordTokenSeen := true }
        continue
      /- 1.4.2 -/
      let encodedCodePoints := utf8PercentEncode s!"{c}" PercentEncodeSets.userinfo
      /- 1.4.3 -/
      if (← get).passwordTokenSeen then modify fun m => {
        m with
        url := {
          m.url with
          password :=
            match m.url.password with
            | none => encodedCodePoints
            | some x => x.append encodedCodePoints
        }
      }
      /- 1.4.4 -/
      else modify fun m => {
        m with
        url := {
          m.url with
            username :=
              match m.url.username with
              | none => encodedCodePoints
              | some x => x.append encodedCodePoints
        }
      }
    /- 1.5 -/
    modify fun m => { m with buffer := "" }
    return
  else if c?.isNone || (c? == some '\u002F' || c? == some '\u003F' || c? == some '\u0023') || ((← get).url.isSpecial && c? == some '\u005C')
  then
    if (← get).atSignSeen && (← get).buffer == ""
    then
      modify fun m => { m with errorLog := m.errorLog.push (.hostMissing, m.pointer, some sourceLoc!)}
      throw sourceLoc!
    modify fun m => {
      m with
      pointer := m.pointer - (m.buffer.length + 1)
      buffer := ""
      state := host
    }
  else
    modify fun m => { m with buffer := m.buffer.push c?.get! }

def portState : ParserM Unit := do
  let c? ← curr?
  if (c?.map (fun c => c.isDigit)).getD false
  then
    modify fun m => { m with buffer := m.buffer.push c?.get! }
    return
  /- 2. -/
  else if c?.isNone || c? == some '\u002F' || c? == some '\u003F' || c? == some '\u0023'
    || ((← get).url.isSpecial && c? == some '\u005C')
    || (← get).stateOverride.isSome
  then
    if (← get).buffer != ""
    then
      /- 1. -/
      let parsed : Option UInt16 := (← get).buffer.toNat?.bind (fun x => if x < UInt16.size then UInt16.ofNat x else none)
      match parsed with
      | none => throw s!"bad port error in portState: {sourceLoc!}"
      | some port_ =>
        /- 3. -/
        modify fun m => {
          m with
          url := {
            m.url with
            port := if m.url.isDefaultPortForScheme' port_ then none else some port_
          }
        }
        /- 4. -/
        modify fun m => { m with buffer := "" }
        /- 5. -/
        if (← get).stateOverride.isSome then return
    /- 2. 2. -/
    if (← get).stateOverride.isSome
    then throw s!"bad state override in portState: {sourceLoc!}"
    /- 3. -/
    modify fun m => { m with state := pathStart, pointer := m.pointer - 1 }
  else
    modify fun m => { m with errorLog := m.errorLog.push (.portValidationError, m.pointer, some sourceLoc!)}
    throw s!"port validation error: {sourceLoc!}"

def pathStartState : ParserM Unit := do
  let c? ← curr?
  let stateOverride? := (← get).stateOverride
  /- 1. -/
  if (← get).url.isSpecial
  then
    /- 1.1 -/
    if c? == '\u005C' then modify fun m => { m with errorLog := m.errorLog.push (.invalidReverseSolidus, m.pointer, some sourceLoc!)}
    /- 1.2 -/
    modify fun m => { m with state := path }
    /- 1.3 -/
    if c? != some '\u002F' && c? != some '\u005C' then modify fun m => { m with pointer := m.pointer - 1 }
  /- 2. -/
  else if stateOverride?.isNone && c? == some '\u003F'
  then
    modify fun m => { m with
      state := query
      url := {
        m.url with query := ""
      }
    }
  /- 3. -/
  else if stateOverride?.isNone && c? == some '\u0023'
  then
    modify fun m => { m with
      state := fragment
      url := {
        m.url with fragment := ""
      }
    }
  /- 4. -/
  else if c?.isSome
  then
    modify fun m => { m with
      state := path
      pointer := if c? != '\u002F' then m.pointer - 1 else m.pointer
    }
  /- 5. -/
  else if stateOverride?.isSome && (← get).url.host.isNone then
    appendPath ""


/-
A Windows drive letter is two code points, of which the first is an ASCII alpha and the second is either U+003A (:) or U+007C (|).
-/
def isWindowsDriveLetter (s : String) : Bool :=
  match s.toList with
  | fst :: snd :: [] => fst.isAlpha && (snd == '\u003A' || snd == '\u007C')
  | _ => false

/-
A normalized Windows drive letter is a Windows drive letter of which the second code point is U+003A (:).

As per the URL writing section, only a normalized Windows drive letter is conforming.
-/
def isNormalizedWindowsDriveLetter (s : String) : Bool :=
  s.isWindowsDriveLetter && s.toList[1]? == some ':'

/-
A string starts with a Windows drive letter if all of the following are true:

    its length is greater than or equal to 2
    its first two code points are a Windows drive letter
    its length is 2 or its third code point is U+002F (/), U+005C (\), U+003F (?), or U+0023 (#).
-/
def startsWithWindowsDriveLetter (s : String) : Bool :=
  let xs := s.toList
  if xs.length < 2
  then false
  else
    match xs with
    | fst :: snd :: rest =>
      fst.isAlpha && (snd == '\u003A' || snd == '\u007C') &&
        match rest with
        | [] => true
        | trd :: _ => trd == '\u002F' || trd == '\u005C' || trd == '\u003F' || trd == '\u0023'
    | _ => false

def shortenUrlPath : ParserM Unit := do
  let url := (← get).url
  match url.path with
  | .inl _ => throw s!"assert not opaque path in shorten"
  | .inr pathSegments =>
    let driveLetterBool : Bool :=
      match pathSegments[0]? with
      | none => false
      | some x => x.isNormalizedWindowsDriveLetter
    if url.isFile && pathSegments.size = 1 && driveLetterBool
    then
      return
    else
      modify fun m => {
        m with
        url := { m.url with path := .inr pathSegments.pop }
      }

def pathState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if
    (c?.isNone) || (c? == '\u002F') ||
    ((← get).url.isSpecial && c? == some '\u005C') ||
    ((← get).stateOverride.isNone && ( c? == some '\u003F'|| c? == some '\u0023'))
  then
    /- 1.1 -/
    if (← get).url.isSpecial && c? == '\u005c' then modify fun m => { m with errorLog := m.errorLog.push (.invalidReverseSolidus, m.pointer, some sourceLoc!)}
    /- 1.2 -/
    if isDoubleDotURLPathSegment (← get).buffer
    then
      if (← get).url.opaquePath then throw s!"assert no opaque path: {sourceLoc!}"
      /- 1.2.1 -/
      let _ ← shortenUrlPath
      /- 1.2.2 -/
      if c? != '\u002F' && !(((← get).url.isSpecial) && c? == some '\u005C')
      then
        let _ ← appendPath ""
    /- 1.3 -/
    else if
      isSingleDotURLPathSegment (← get).buffer &&
      !((c? == '\u002F') || ((← get).url.isSpecial && c? == some '\u005C'))
    then
      let _ ← appendPath ""
    /- 1.4 -/
    else if !(isSingleDotURLPathSegment (← get).buffer)
      then
        /- 1.4.1 -/
        if (← get).url.isFile && ( ← get).url.pathIsEmpty && isWindowsDriveLetter (← get).buffer
        then
          modify fun m => { m with buffer := m.buffer.modify ⟨1⟩ (fun _ => '\u003A') }
        let _ ← appendPath (← get).buffer
    /- 1.5 -/
    modify fun m => { m with buffer := "" }
    /- 1.6 -/
    if c? == some '\u003F' then modify fun m => { m with
      state := query
      url := {
        m.url with
          query := ""
      }
    }
    /- 1.7 -/
    if c? == some '\u0023' then modify fun m => { m with
      state := fragment
      url := { m.url with fragment := "" }
    }
  /- 2. -/
  else
    if c? != '\u0025' && !(c?.map (fun x => x.isUrlCodePoint)).getD false then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some sourceLoc!)}
    let next1 := ((← peekNext1).map (fun c => c.isASCIIHexDigit)).getD false
    let next2 := ((← peekNext2).map (fun c => c.isASCIIHexDigit)).getD false
    if c? == some '\u0025' && !(next1 && next2) then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some sourceLoc!)}
    let pencode := utf8PercentEncode s!"{c?.get!}" PercentEncodeSets.path
    modify fun m => { m with buffer := m.buffer.append pencode }

def opaquePathState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if c? == some '\u003F' then modify fun m => {
    m with
    state :=  query
    url := { m.url with query := "" }
  }
  /- 2. -/
  else if c? == '\u0023'
  then
    modify fun m => {
      m with
      url := { m.url with fragment := ""}
      state := fragment
    }
  /- 3. -/
  else if c? == some '\u0020'
  then
    let peek? ← peekNext1
    /- 3.1, 3.2 -/
    if peek? == some '?' || peek? == some '#'
    then
      let _ ← appendPath "%20"
    else
      let _ ← appendPath " "
  /- 4. -/
  else if c?.isSome
  then
    let c := c?.get!
    /- 4.1 -/
    if !(c.isUrlCodePoint) && c != '\u0025' then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some sourceLoc!)}
    /- 4.2 -/
    let peek1 := ((← peekNext1).map (fun c => c.isASCIIHexDigit)).getD false
    let peek2 := ((← peekNext2).map (fun c => c.isASCIIHexDigit)).getD false
    if c == '\u0025' && !(peek1 && peek2) then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some sourceLoc!)}
    let r := utf8PercentEncode s!"{c}" PercentEncodeSets.c0Controls
    appendPath r

def remStartsW2ASCIIHex : ParserM Bool := do
    let peek1 := ((← peekNext1).map (fun c => c.isASCIIHexDigit)).getD false
    let peek2 := ((← peekNext2).map (fun c => c.isASCIIHexDigit)).getD false
    return (peek1 && peek2)

def queryState : ParserM Unit := do
  let encoding := (← read).queryEncodingOverride
  let c? ← curr?
  /- 1. -/
  if encoding.isSome && (!(← get).url.isSpecial || (← get).url.isWsOrWss)
  then
    throw s!"alternative encodings not supported: {sourceLoc!}"
  /- 2. -/
  else if ((← get).stateOverride.isNone && c? == some '\u0023') || c?.isNone
  then
    /- 2.1 -/
    let queryPercentEncodeSet := if (← get).url.isSpecial then PercentEncodeSets.specialQuery else PercentEncodeSets.query
    /- 2.2 -/
    let encoded ←
      match percentEncodeAfterEncoding "utf-8" (← get).buffer queryPercentEncodeSet with
      | .error _e => throw s!"failed to encode query: {sourceLoc!}"
      | .ok encoded => pure encoded
    appendQuery encoded
    /- 2.3 -/
    modify fun m => { m with buffer := "" }
    /- 2.4 -/
    if c? == some '\u0023'
    then modify fun m => { m with state := fragment, url := { m.url with fragment := "" }}
  /- 3. -/
  else if c?.isSome
  then
    if !(c?.get!.isUrlCodePoint) && c? != some '\u0025' then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some sourceLoc!)}
    if c? == some '\u0025' && !(← remStartsW2ASCIIHex) then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some sourceLoc!)}
    modify fun m => { m with buffer := m.buffer.append s!"{c?.get!}" }

def fragmentState : ParserM Unit := do
  match (← curr?) with
  | none => return
  | some c =>
    /- 1.1 -/
    if !c.isUrlCodePoint && c != '\u0025' then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some "fragment 0")}
    /- 1.2 -/
    if c == '\u0025' && !(← remStartsW2ASCIIHex) then modify fun m => { m with errorLog := m.errorLog.push (.invalidUrlUnit, none, some "fragment 1")}
    /- 1.3 -/
    let encoded := utf8PercentEncode s!"{c}" PercentEncodeSets.fragment
    modify fun m => {
      m with
      url := {
        m.url with
        fragment :=
          match m.url.fragment with
          | none => some encoded
          | some s => some (s.append encoded)
      }
    }

def relativeState : ParserM Unit := do
  /- 1. -/
  if ((← get).base.map (Url.isFile)).getD false then throw s!"assert not file: {sourceLoc!}"
  /- 2. -/
  let base := (← get).base.get!
  modify fun m => { m with url := { m.url with scheme := base.scheme }}
  let c? ← curr?
  /- 3. -/
  if c? == some '\u002F' then modify fun m => { m with state := relativeSlash }
  /- 4. -/
  else if (← get).url.isSpecial && c? == some '\u005C'
    then modify fun m => { m with state := relativeSlash, errorLog := m.errorLog.push (.invalidReverseSolidus, none, some sourceLoc!)}
  else
    /- 5.1 -/
    modify fun m => {
      m with
      url := {
        m.url with
        username := base.username
        password := base.password
        host := base.host
        port := base.port
        path := base.path
        query := base.query
      }
    }
    /- 5.2 -/
    if c? == some '\u003F'
    then modify fun m => { m with url := { m.url with query := ""}, state := query }
    /- 5.3 -/
    else if c? == some '\u0023'
    then modify fun m => { m with url := { m.url with fragment := "" }, state := fragment }
    /- 5.4 -/
    else if c?.isSome
    then
      /- 5.4.1 -/
      modify fun m => { m with url := { m.url with query := none }}
      /- 5.4.2 -/
      let _ ← shortenUrlPath
      modify fun m => { m with state := path, pointer := m.pointer - 1 }

def fileState : ParserM Unit := do
  let c? ← curr?
  /- 1., 2. -/
  modify fun m => { m with url := { m.url with scheme := "file", host := some (LeanUrl.Host.empty) }}
  /- 3. -/
  if c? == '\u002F' || c? == '\u005C'
  then
    /- 3.1 -/
    if c? == some '\u005C' then modify fun m => { m with errorLog := m.errorLog.push (.invalidReverseSolidus, none, some sourceLoc!)}
    modify fun m => { m with state := fileSlash }
  /- 4. -/
  else if ((← get).base.map Url.isFile).getD false
  then
    let base := (← get).base.get!
    /-4.1 -/
    modify fun m => {
      m with url := {
        m.url with
        host := base.host
        path := base.path
        query := base.query
      }
    }
    /- 4.2 -/
    if c? == some '\u003F'
    then modify fun m => { m with state := query, url := { m.url with query := "" }}
    /- 4.3 -/
    else if c? == some '\u0023' then modify fun m => { m with state := fragment, url := { m.url with fragment := "" }}
    /- 4.4 -/
    else if c?.isSome
    then
      /- 4.4.1 -/
      modify fun m => { m with url := { m.url with query := none }}
      /- 4.4.2 -/
      let some rem ← remaining | throw s!"early EOF: {sourceLoc!}"
      if !startsWithWindowsDriveLetter rem
      then
        let _ ← shortenUrlPath
      else
        /- 4.4.3.1 -/
        modify fun m => { m with errorLog := m.errorLog.push (.fileInvalidWindowsDriveLetter, none, sourceLoc!) }
        /- 4.4.3.2 -/
        modify fun m => { m with url := { m.url with path := .inr #[] }}
      /- 4.4.4 -/
      modify fun m => { m with state := path, pointer := m.pointer - 1 }
  /- 5. -/
  else
    modify fun m => { m with state := path, pointer := m.pointer - 1 }

def fileSlashState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if c? == some '\u002F' || c? == '\u005C'
  then
    /- 1.1 -/
    if c? == some '\u005c' then modify fun m => { m with errorLog := m.errorLog.push (.invalidReverseSolidus, none, some sourceLoc!)}
    modify fun m => { m with state := fileHost }
  /- 2. -/
  else
    /- 2.1 -/
    if ((← get).base.map Url.isFile).getD false
    then
      let base := (← get).base.get!
      /- 2.1.1 -/
      modify fun m => { m with url := { m.url with host := base.host }}
      /- 2.1.2 -/
      let some rem ← remaining | throw s!"early EOF: {sourceLoc!}"
      let doesntStartWith := !startsWithWindowsDriveLetter rem
      let basePath0Is :=
        match base.path with
        | .inl _ => false
        | .inr xs =>
          (xs[0]?.map (fun path => isNormalizedWindowsDriveLetter path)).getD false

      if doesntStartWith && basePath0Is
      then
        let toPush :=
          match base.path with
          | .inr xs => xs[0]!
          | _ => panic "should be unreachable"
        let _ ← appendPath toPush
    modify fun m => { m with state := path, pointer := m.pointer - 1 }

def fileHostState : ParserM Unit := do
  let c? ← curr?
  /- 1. -/
  if c?.isNone || c? == some '\u002F' || c? == some '\u005C' || c? == some '\u003F' || c? == some '\u0023'
  then
    modify fun m => { m with pointer := m.pointer - 1 }
    /- 1.1 -/
    if (← get).stateOverride.isNone && (isWindowsDriveLetter (← get).buffer)
    then
      modify fun m => { m with state := path, errorLog := m.errorLog.push (.fileInvalidWindowsDriveLetter, none, sourceLoc!)}
    /- 1.2 -/
    else if (← get).buffer.isEmpty
    then
      /- 1.2.1 -/
      modify fun m => { m with url := { m.url with host := some (LeanUrl.Host.empty) }}
      /- 1.2.2 -/
      if (← get).stateOverride.isSome then return
      /- 1.2.3 -/
      modify fun m => { m with state := pathStart }
    /- 1.3 -/
    else
      let host ←
        match LeanUrl.Parser.Host.parseWwg (← get).buffer.toArray false with
        | .ok a => if a.isLocalhost then pure (LeanUrl.Host.empty) else pure a
        | .error _e => throw s!"{sourceLoc!}"
      modify fun m => { m with url := { m.url with host := host }}
      if (← get).stateOverride.isSome then return
      modify fun m => { m with buffer := "", state := pathStart }
  else
    modify fun m => { m with buffer := m.buffer.append s!"{c?.get!}" }

partial def basicParserRec : ParserM Unit := do
  match (← get).state with
    | schemeStart => schemeStartState
    | scheme => schemeState
    | noScheme => noSchemeState
    | specialRelativeOrAuthority => specialRelativeOrAuthorityState
    | pathOrAuthority => pathOrAuthorityState
    | specialAuthoritySlashes => specialAuthoritySlashesState
    | specialAuthorityIgnoreSlashes => specialAuthorityIgnoreSlashesState
    | authority => authorityState
    | relativeSlash => relativeSlashState
    | host | hostName => hostState
    | port => portState
    | pathStart => pathStartState
    | path => pathState
    | opaquePath => opaquePathState
    | relative => relativeState
    | query => queryState
    | fragment => fragmentState
    | file => fileState
    | fileSlash => fileSlashState
    | fileHost => fileHostState
  let st ← get
  if st.pointer < st.input.size
  then
    modify fun st => {st with pointer := st.pointer + 1}
    basicParserRec

def parseUrlAux
  (input : String)
  (base url : Option Url := none)
  (stateOverride : Option State := none)
  (methods : Option Methods := none)
  : EStateM.Result String Machine Url :=
  let (s, a) := trimc0ControlSpace input
  let (s, b) := trimTabNewlineCarriageReturn s
  let errorLog := if let some a := a then #[a] else #[]
  let errorLog := if let some b := b then errorLog.push b else errorLog

  let st : Machine := {
    base := base
    url := url.getD Inhabited.default
    errorLog
    input := s.toArray
    pointer := 0
    stateOverride
    state := stateOverride.getD schemeStart
  }
  match basicParserRec (methods.getD Inhabited.default) |>.run st with
  | .error e s => .error e s
  | .ok _ s =>
    if let .error e := s.url.rule_4_1_Ck then .error e s
    else if let .error e := s.url.rule_4_2_Ck then .error e s
    else .ok s.url s

def parseUrl
  (input : String)
  (base : Option String)
  (stateOverride : Option State := none)
  (methods : Option Methods := none)
  : EStateM.Result String Machine Url :=
  match base with
  | none => parseUrlAux input (stateOverride := stateOverride) (methods := methods)
  | some baseString =>
    match parseUrlAux (input := baseString) (base := none) (url := none) (methods := methods) with
    | .ok baseUrl _ => parseUrlAux input (base := baseUrl) (stateOverride := stateOverride) (methods := methods)
    | e@(.error _ _) => e

def parseUrl'
  (input : String)
  (base : Option String)
  (stateOverride : Option State := none)
  (methods : Option Methods := none)
  : Except String Url :=
  match parseUrl input base stateOverride methods with
  | .error e _ => .error e
  | .ok _ s => .ok s.url
