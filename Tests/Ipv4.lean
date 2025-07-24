import LeanUrl.Parser.Ipv4

open LeanUrl

open Parser

/-- info: Except.ok 2130706432 -/
#guard_msgs in
#eval Ipv4.parseUInt32 "127.0.0.0"

/-- info: Except.ok "127.0.0.0" -/
#guard_msgs in
#eval (Ipv4.parse "127.0.0.0").map (·.toString)



/-- info: Except.ok 2132218375 -/
#guard_msgs in #eval Ipv4.parseUInt32 "127.23.18.7"

#guard !(Ipv4.parseUInt32 "256.256.256.256.256.").isOk
#guard !(Ipv4.parseUInt32 s!"{UInt32.size}").isOk
#guard !(Ipv4.parseUInt32 "0xffffffff1").isOk

#guard !(Ipv4.parseUInt32 "foo.0x4").isOk
