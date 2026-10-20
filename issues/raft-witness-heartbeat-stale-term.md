---
upstream: unchecked
---

# The witness answers a heartbeat of a newer term with its old term

**Status**: a wrong result, harmless to safety (a liveness hiccup): raft#168's witness, as rebased
on the fork's `raft-witness-goose-lean` (commit `edd87c48`).

**Where**: `witness.go`, `Process`: for a `MsgHeartbeat` with `m.Term > w.state`'s term, `st :=
w.cloneState()`, `w.processMessageWithNewerTerm(m, st)` raises `st`'s term to `m.Term`, then
`resp = w.handleHeartbeat(m)`, which answers with `w.state.GetState().GetTerm()`: the term of the
state read before the raise.

**What happens**: the `MsgHeartbeatResp` carries the witness's old term, below the leader's; the
leader drops a response of an older term, so that heartbeat goes unanswered although the witness
then stores the leader's term (`state.Update(st)`). The next heartbeat (now of the stored term) is
answered. Under check-quorum the leader can miss the witness's activity for one round.
`handleAppend` had the same pattern and was fixed (it answers with `st`'s term; see
`notes/raft-witness-vs-pr168.md`).

**Expected**: the response carries the term the witness now has, `m.Term` (`st`'s).

**How the proof handles it**: the spec of `handleHeartbeat` states the answer at `w.state`'s term
(`wHeartbeat`, `InvWitnessM.lean`), as the code does, and `wStep` (`Process`'s model) answers a
newer-term heartbeat that way; W2's `wGhost_heartbeat` covers the answer at the stored term only,
so a proof of `Process` has to justify this answer (an old-term response) separately.

**Possible fixes**: in `Process`, `case raftpb.MsgHeartbeat: resp = w.handleHeartbeatAt(m,
st.GetState().GetTerm())`, or answer the heartbeat after the update from `w.state = st`.

**Found**: 2026-10-20, modelling `Process` (`wStep`, W3a, witness support).
