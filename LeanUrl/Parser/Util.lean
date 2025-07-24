
inductive SyntaxViolation
  | c0SpaceIgnored
  | tabOrNewlineIgnored
  | expectedDoubleSlash
  | expectedFileDoubleSlash
  | backslash
  | fileWithHostAndWindowsDrive
  | specialSchemeMissingFollowingSolidus
  | missingSchemeNonRelativeURL
  | invalidReverseSolidus
  | invalidCredentials
  | hostMissing
  | portValidationError
  | hostInvalidCodePoint
  | invalidUrlUnit
  | ipv6TooFewPieces
  | ipv6InvalidCompression
  | ipv6TooManyPieces
  | ipv4InIpv6InvalidCodePoint
  | ipv4InIpv6TooManyPieces
  | ipv4EmptyPart
  | ipv4TooManyParts
  | ipv4NonNumericPart
  | ipv4NonDecimalPart
  | ipv4InIpv6OutOfRange
  | ipv4InIpv6TooFewPieces
  | ipv4OutOfRange
  | ipv6MultipleCompressionValidationError
  | ipv6Unclosed
  | ipv6InvalidCodePoint
  | hostEarlyEOF
  | fileInvalidWindowsDriveLetter
  | domainInvalidCodePoint
deriving BEq, Repr, Inhabited

abbrev SyntaxViolationLog := (SyntaxViolation × Option Int × Option String)
