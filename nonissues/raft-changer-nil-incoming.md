---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---
# raft: a `confchange.Changer` over a tracker with a nil incoming voter map panics on `AddNode`

A `confchange.Changer` whose `Tracker` is a `tracker.ProgressTracker` literal (incoming voter map
`Voters[0]` nil) panics with "assignment to entry in nil map" on the first `AddNode`: `makeVoter`
and `initProgress` write into the map without allocating it, unlike the learner sets
(`nilAwareAdd`). `tracker.MakeProgressTracker` allocates it, and raft only builds its trackers
that way.

**Why not an issue:** a precondition raft's own callers meet: the test builds the tracker as a
literal, which no raft or etcd caller does (etcd never uses `confchange` directly); at most worth
documenting.

`TestChangerNilIncomingVoters` in
[`nonissues/raft-changer-nil-incoming/changer_nil_incoming_test.go`](raft-changer-nil-incoming/changer_nil_incoming_test.go)
(package `confchange`) fails at etcd-io/raft@c51f010c851e, go1.27.3: `Panic value: assignment to
entry in nil map`.

## Proof

no: `ownCfgCC` (`Proof/go_etcd_io/raft/v3/InvConfchange.lean`) requires the incoming voter map to
be a map, which every tracker raft builds satisfies.

## Notes

The 2026-10-23 review's Plan: "Nonissue." A fix would allocate the map in `checkAndCopy` or
`initProgress`, as `nilAwareAdd` does for learners.
