---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---
# raft: the `with_tla` trace of a sent `MsgApp` records the sender's own progress, not the target's

raft's trace instrumentation (`state_trace.go`, built with the `with_tla` tag) logs each sent
`MsgApp` with `match` and `next` properties meant to describe the follower the message is for, but
reads them from `r.trk.Progress[m.GetFrom()]`: the leader's progress of itself. The values logged
are the leader's own last index and next index, the same for every follower.

**Why not an issue:** found by code reading (no test), and nothing reads those properties:
`Traceetcdraft.tla` matches a `SendAppendEntriesRequest` line by the message's fields only, and
etcd's trace validation (`etcd-io/raft`'s `tla/` tooling) ignores `match`/`next`. A trace consumer
that used them would be misled; the fix is `r.trk.Progress[m.GetTo()]`
([`state_trace.go`](https://github.com/etcd-io/raft/blob/b867cf1318b67a6ba5e8a10ac5da0fb7a1cc4b9e/state_trace.go#L295-L301),
raft v3.7.0, as `.lake/goose/raft/state_trace.go:296-300` of the verified fork).

## Proof

no: `SendEvOf` (`Proof/go_etcd_io/raft/v3/TracedHooksDraft.lean`) leaves the properties `match` and
`next` unconstrained, and `ConvertEvents` does not copy them (`examples/raft/tracecheck/main.go`).
Recorded in `notes/trace-validation-hooks.md` ("An instrumentation detail"); flagged by the S5 Draft's
review round 3 (`notes/trace-validation-reviews/s5-r3.md`, "Go code").
