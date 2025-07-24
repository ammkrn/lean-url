import LeanUrl.Util
import LeanUrl.Parser.Util
import Std.Data.HashSet

open Std (HashSet)

set_option linter.unusedVariables false

/-
1. punycode
2. idna
3. preprocessing section 4 + IDNA mapping table (section 5)
4. unicodeToASCII/unicodeToUnicode

*domainToAscii* is defined in whatwg, but it depends on unicodeToASCII

*domainToUnicode* is also in whatwg, relies on unicode to unicode
-/

/-
 4.2 ToASCII

The operation corresponding to ToASCII of [RFC3490] is defined by the following steps:

Input

    A prospective domain_name expressed as a sequence of Unicode code points
    A boolean flag: CheckHyphens
    A boolean flag: CheckBidi
    A boolean flag: CheckJoiners
    A boolean flag: UseSTD3ASCIIRules
    A boolean flag: Transitional_Processing (deprecated)
    A boolean flag: VerifyDnsLength
    A boolean flag: IgnoreInvalidPunycode

Processing

    To the input domain_name, apply the Processing Steps in Section 4, Processing, using the input boolean flags Transitional_Processing, CheckHyphens, CheckBidi, CheckJoiners, and UseSTD3ASCIIRules. This may record an error.
    Break the result into labels at U+002E FULL STOP.
    Convert each label with non-ASCII characters into Punycode [RFC3492], and prefix by “xn--”. This may record an error.
    If the VerifyDnsLength flag is true, then verify DNS length restrictions. This may record an error. For more information, see [STD13] and [STD3].
        The length of the domain name, excluding the root label and its dot, is from 1 to 253.
        The length of each label is from 1 to 63.
            Note: Technically, a complete domain name ends with an empty label for the DNS root (see [STD13] [RFC1034] section 3). This empty label, and the trailing dot, is almost always omitted.
            When VerifyDnsLength is false, the empty root label is passed through.
            When VerifyDnsLength is true, the empty root label is disallowed. This corresponds to the syntax in [RFC1034] section 3.5 Preferred name syntax which also defines the label length restrictions.
    If an error was recorded in steps 1-4, then the operation has failed and a failure value is returned. No DNS lookup should be done.
    Otherwise join the labels using U+002E FULL STOP as a separator, and return the result.

Implementations are advised to apply additional tests to these labels, such as those described in Unicode Technical Report #36, Unicode Security Considerations [UTR36] and Unicode Technical Standard #39, Unicode Security Mechanisms [UTS39], and take appropriate actions. For example, a label with mixed scripts or confusables may be called out in the UI. Note that the use of Punycode to signal problems may be counter-productive, as described in [UTR36].

-/
def unicodeToAscii
  (domainName : String)
  (
    checkHyphens
    checkBidi
    checkJoiners
    useStd3ASCIIRules
    transitionalProcessing
    verifyDnsLength
    ignoreInvalidPunycode
    : Option Bool := none
  )
  : Except String String := .ok domainName


/-

Let result be the result of running Unicode ToASCII with
domain_name set to domain,
CheckHyphens set to beStrict,
CheckBidi set to true,
CheckJoiners set to true,
UseSTD3ASCIIRules set to beStrict,
Transitional_Processing set to false,
VerifyDnsLength set to beStrict,
and IgnoreInvalidPunycode set to false.
-/

def domainToAscii (domainName : String) (beStrict : Bool) : Except SyntaxViolationLog String :=
  let result := unicodeToAscii
    domainName
    (checkHyphens := some beStrict)
    (checkBidi := some true)
    (checkJoiners := some true)
    (useStd3ASCIIRules := some beStrict)
    (transitionalProcessing := some false)
    (verifyDnsLength := some beStrict)
    (ignoreInvalidPunycode := some false)
  match result with
  | .error e => throw (SyntaxViolation.domainInvalidCodePoint, none, some sourceLoc!)
  | .ok a =>
    if a.any (fun c => c.forbiddenDomainCodePoint)
    then throw (SyntaxViolation.domainInvalidCodePoint, none, some s!"{sourceLoc!}")
    else .ok a


/-
4.3 ToUnicode

The operation corresponding to ToUnicode of [RFC3490] is defined by the following steps:

Input

    A prospective domain_name expressed as a sequence of Unicode code points
    A boolean flag: CheckHyphens
    A boolean flag: CheckBidi
    A boolean flag: CheckJoiners
    A boolean flag: UseSTD3ASCIIRules
    A boolean flag: Transitional_Processing (deprecated)
    A boolean flag: IgnoreInvalidPunycode

Processing

    To the input domain_name, apply the Processing Steps in Section 4, Processing, using the input boolean flags Transitional_Processing, CheckHyphens, CheckBidi, CheckJoiners, and UseSTD3ASCIIRules. This may record an error.
    Like [RFC3490], this will always produce a converted Unicode string. Unlike ToASCII of [RFC3490], this always signals whether or not there was an error.

Implementations are advised to apply additional tests to these labels, such as those described in Unicode Technical Report #36, Unicode Security Considerations [UTR36] and Unicode Technical Standard #39, Unicode Security Mechanisms [UTS39], and take appropriate actions. For example, a label with mixed scripts or confusables may be called out in the UI. Note that the use of Punycode to signal problems may be counter-productive, as described in [UTR36].
-/
def unicodeToUnicode
  (domainName : String)
  (
    checkHyphens
    checkBidi
    checkJoiners
    useStd3ASCIIRules
    transitionalProcessing
    ignoreInvalidPunycode
    : Option Bool := none
  ) : Except String String := .ok domainName


/-
Let result be the result of running Unicode ToUnicode with
domain_name set to domain,
CheckHyphens set to beStrict,
CheckBidi set to true,
CheckJoiners set to true,
UseSTD3ASCIIRules set to beStrict,
Transitional_Processing set to false,
and IgnoreInvalidPunycode set to false.
-/

def domainToUnicode (domainName : String) (beStrict : Bool) : Except String String :=
  unicodeToUnicode
    domainName
    (checkHyphens := some beStrict)
    (checkBidi := some true)
    (checkJoiners := some true)
    (useStd3ASCIIRules := some beStrict)
    (transitionalProcessing := some false)
    (ignoreInvalidPunycode := some false)
