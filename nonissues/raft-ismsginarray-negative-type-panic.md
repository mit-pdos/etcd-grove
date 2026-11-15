---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---
# raft: `IsLocalMsg` and `IsResponseMsg` panic on a negative `MessageType`

`isMsgInArray` converts the `int32` message type with `int(msgt)`, which keeps the sign, and checks
only `i < len(arr)` before indexing
([util.go](https://github.com/etcd-io/raft/blob/b867cf13/util.go#L54-L57)): for a negative type the
check passes and `arr[i]` panics with an index out of range. So the exported
`raft.IsLocalMsg(pb.MessageType(-1))` and `raft.IsResponseMsg(pb.MessageType(-1))` panic instead of
returning `false`.

**Why not an issue:** found by code reading, no test; unreachable through etcd: a message decoded
from the wire has a known type (raftpb is proto2 with a closed enum), and raft's own messages carry
its constants. The specs take `0 ≤ msgt` as a premise (`SpecPlan/Spec/go_etcd_io/raft/v3/isMsgInArray.lean`;
R1's `IsLocalMsg`/`IsResponseMsg`).

## Proof

no: the premise `0 ≤ sint.Z t` of `isMsgInArray.spec`, met by every caller.
