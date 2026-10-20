---
upstream: unchecked
---

# `witness.Process` panics when the storage's `WitnessState.GetState()` returns nil

**Status**: an unstated precondition of the `WitnessStorage` API (raft#168's witness, as rebased
on the fork's `raft-witness-goose-lean`, commit `edd87c48`). **Fixed in the fork**, commit
`9ed005d46` (`cloneState` reads through the nil-safe getters; test `TestWitnessNilStoredState`);
row 14 of `notes/raft-witness-vs-pr168.md`.

**Where**: `witness.go`, `Process` (`w.state = state.GetState()`, then `w.cloneState()`) and
`cloneState` (`len(w.state.ReplicationSet)`, `copy(st.ReplicationSet, w.state.ReplicationSet)`).
`WitnessState.GetState() *raftpb.WitnessHardState` says nothing about nil.

**What happens**: every other read of `w.state` goes through the generated nil-safe getters
(`w.state.GetState().GetTerm()`, `w.state.GetLastLogTerm()`), so a nil state reads as the zero
state, as for the witness before its first read. `cloneState` reads the field
`w.state.ReplicationSet` directly: with a nil `w.state` this is a nil-pointer dereference. A
storage that represents "nothing stored yet" by a nil `*WitnessHardState` (natural for a fresh
storage object) makes the first request that is not answered from the cache, such as a vote
request, panic in `cloneState`.

**Expected**: either `GetState` documents that it never returns nil (a fresh storage returns
`&raftpb.WitnessHardState{}`), or `cloneState` reads through `GetReplicationSet()` /
`GetReplicationSetOutgoing()`, which are nil-safe.

**How the proof handles it**: the proof is of the fixed code: the storage contract (`isWState`,
`InvWitnessStorage.lean`) lets `GetState` return nil (`whsOpt`, the zero state), and
`cloneState`'s spec takes `whsOpt`. (Before the fix, the spec required `whsRO`, non-nil.)

**Possible fixes**: `make([]uint64, len(w.state.GetReplicationSet()))` and `copy(st.ReplicationSet,
w.state.GetReplicationSet())` (and the same for the outgoing set), or document the precondition
on `WitnessState.GetState`.

**Found**: 2026-10-20, writing `cloneState`'s spec (W3a, witness support).
