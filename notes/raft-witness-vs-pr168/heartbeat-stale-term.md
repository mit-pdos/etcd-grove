# The witness answers a heartbeat of a newer term with its old term

*A defect of etcd-io/raft#168 as rebased on the fork `raft-witness-goose-lean`, not of raft's or etcd's main branches: recorded here, not in `issues/` (which is for the main branches). Summary row in `notes/raft-witness-vs-pr168.md`.*

**Status**: a wrong result, harmless to safety (a liveness hiccup): raft#168's witness, as rebased
on the fork's `raft-witness-goose-lean` (commit `edd87c48`). **Fixed in the fork**, commit
`9ed005d46` (`handleHeartbeat(m, term)`; test `TestWitnessHeartbeatNewerTermResponse`); row 13 of
`notes/raft-witness-vs-pr168.md`.

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

**How the proof handles it**: the proof is of the fixed code: `handleHeartbeat`'s spec answers at
the term it is passed (`wHeartbeat id term`, `InvWitnessM.lean`), and `wStep` (`Process`'s model)
passes the stored state's term on the early path and the raised state's on the newer-term path.

**Possible fixes**: in `Process`, `case raftpb.MsgHeartbeat: resp = w.handleHeartbeatAt(m,
st.GetState().GetTerm())`, or answer the heartbeat after the update from `w.state = st`.

**Found**: 2026-10-20, modelling `Process` (`wStep`, W3a, witness support).
