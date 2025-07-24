import LeanUrl.Parser.Ipv6

open LeanUrl
open Parser

/-- info: "[0:f::f:f:0:0]" -/
#guard_msgs in #eval Host.serialize (Host.ipAddr (.v6 ⟨#v[0, 0xf, 0, 0, 0xf, 0xf, 0, 0]⟩))

/-- info: "[1::]" -/
#guard_msgs in #eval Host.serialize (Host.ipAddr (.v6 ⟨#v[1, 0, 0, 0, 0, 0, 0, 0]⟩))

/-- info: "[::7f00:1]" -/
#guard_msgs in #eval Host.serialize (Host.ipAddr (.v6 ⟨#v[0, 0, 0, 0, 0, 0, 32512, 1]⟩))

/-- info: "7f00" -/
#guard_msgs in #eval printHex 32512


--#eval Ipv6.parse "2607:f0d0:1002:51::4".toArray
--#eval Ipv6.parse "2607:f0d0:1002:51::4".toArray
--#eval Ipv6.parse "::127.0.0.1".toArray
--#eval Ipv6.parse "1:2:0:0:0:0:0:3".toArray
--#eval Ipv6.parse "256.256.256.256.256.".toArray
--#eval Ipv6.parse "0:f::f:f:0:0".toArray
--#eval Ipv6.parse "1:2:0:0:5:0:0:0".toArray
--#eval Ipv6.parse "1:0:0:0:0:0:0:0".toArray

/-- info: "0:f::f:f:0:0" -/
#guard_msgs in #eval serializeIpv6 ⟨#v[0, 0xf, 0, 0, 0xf, 0xf, 0, 0]⟩
/-- info: "1:2:0:0:5::" -/
#guard_msgs in #eval serializeIpv6 ⟨#v[1, 2, 0, 0, 5, 0, 0, 0]⟩
/-- info: "1::" -/
#guard_msgs in #eval serializeIpv6 ⟨#v[1, 0, 0, 0, 0, 0, 0, 0]⟩
