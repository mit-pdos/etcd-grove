---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/raft#397 pr merged: introduced the 8-byte heartbeat context (the read queue's position) that `recvAck` decodes without checking its length
blocks-proof: no
---
# raft: a leader panics on a heartbeat response whose context is shorter than 8 bytes

A leader using `ReadOnlySafe` (the default) panics (`index out of range [7]`) when it steps a
`MsgHeartbeatResp` whose `Context` is non-empty but shorter than 8 bytes: `recvAck` decodes it with
`binary.LittleEndian.Uint64`, which needs 8 bytes. A leader only ever sends `heartbeatCtx`'s 8-byte
contexts (or none), and a follower echoes the heartbeat's context unchanged (`handleHeartbeat`), so
only a malformed or forged peer message carries a shorter one.

**Why not an issue:** input only a misbehaving peer sends: every raft version echoes the leader's
context, and the leader's contexts are its own `heartbeatCtx` (8 bytes) since etcd-io/raft#397;
etcd's peers are trusted (`THREAT_MODEL.md`), and a forged message can do worse anyway (a forged
8-byte ack confirms reads no quorum acknowledged). A rolling upgrade from a raft before #397 does
not reach it either: a response to an old-version leader's heartbeat (which carried the read
request's context) goes back to that leader, and after a restart it arrives at a follower or with
a lower term, both ignored. A length check (ignore a context that is not 8 bytes) would be cheap
hardening.

`TestHeartbeatRespShortContext` in
[`nonissues/raft-heartbeat-resp-short-context-panic/heartbeat_resp_short_context_test.go`](raft-heartbeat-resp-short-context-panic/heartbeat_resp_short_context_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3, fails with
`leader panicked: runtime error: index out of range [7] with length 1`; it also fails at the
pinned fork commit 565c2bda9e6d (same `read_only.go` as v3.7.0).

## Proof

no: `readOnly.recvAck.spec` takes the context empty or at least 8 bytes long
(`SpecPlan/Spec/go_etcd_io/raft/v3/readOnly__recvAck.lean`), which holds for the contexts a leader sends
and its followers echo.
