/-
The witness's logic as pure functions (2026-10-20, witness support, `notes/raft-witness.md`): a
model of `witness.go`'s handlers on the witness's durable state (`raftpb.WitnessHardState`, as
`WHS`) and its requests (`WitnessMessage`, as `WMsg`), each the Go function's result exactly
(`witness__*.lean` prove them). `Process` (the compare-and-swap loop with the cache) is specified
against these and the storage's contract (`Spec/go_etcd_io/raft/v3/witness__Process.lean`).

The responses are raft messages: their scalar fields as a `MessageM` and the context bytes.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

section model
variable [FfiSyntax]

/-- The witness's durable state (`raftpb.WitnessHardState`): its hard state (term, vote,
commit), the last entry it was told of (index, term, subterm), the leader it knows, and the
replication sets (incoming, outgoing) stored with that entry. -/
structure WHS where
  term : w64
  vote : w64
  commit : w64
  li : w64
  lt : w64
  ls : w64
  lead : w64
  rs : List w64
  rsOut : List w64

/-- A witness that has seen nothing (a zero, or nil, `WitnessHardState`). -/
def WHS.zero : WHS := ⟨W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, [], []⟩

/-- A request to the witness (`raft.WitnessMessage`). `votes` is the candidate's vote tally
(granted or rejected: the witness counts the responders, `handleVote`). -/
structure WMsg where
  ty : raftpb.MessageType
  frm : w64
  to : w64
  term : w64
  lt : w64
  ls : w64
  li : w64
  rs0 : List w64
  rs1 : List w64
  votes : GMap w64 Bool
  ctx : List w8

/-- A response: a raft message's scalar fields and its context. -/
abbrev WResp := MessageM × List w8

/-- `(lt, ls)` is strictly below `(lt', ls')`, lexicographically. -/
def ltPair (lt ls lt' ls' : w64) : Prop :=
  uint.Z lt < uint.Z lt' ∨ (lt = lt' ∧ uint.Z ls < uint.Z ls')

instance (lt ls lt' ls' : w64) : Decidable (ltPair lt ls lt' ls') := by
  unfold ltPair; infer_instance

/-- A message with the given scalars and the rest zero. -/
def respM (ty : raftpb.MessageType) (to frm term index : w64) (reject : Bool) : MessageM :=
  MessageM.mk ty to frm term (W64 0) index (W64 0) (W64 0) reject (W64 0)

/-- `processMessageWithOlderTerm`: a request of an older term than the state `σ` (the cached
one). With check-quorum or pre-vote, a heartbeat or append gets a `MsgAppResp` carrying the
newer term (it makes the stale leader step down); a pre-vote a rejection; else nothing. -/
def wOlder (id : w64) (cq pv : Bool) (σ : WHS) (m : WMsg) : Option WResp :=
  if (cq || pv) && decide (m.ty = MsgHeartbeat ∨ m.ty = MsgApp) then
    some (respM MsgAppResp m.frm id σ.term (W64 0) false, [])
  else if m.ty = MsgPreVote then
    some (respM MsgPreVoteResp m.frm (W64 0) σ.term (W64 0) true, [])
  else none

/-- `processMessageWithNewerTerm` on the state being built: a pre-vote changes nothing; a
leader's message (append, heartbeat, snapshot) moves to its term with it as the leader, any
other to the term with none; the vote is cleared. -/
def wNewer (st : WHS) (m : WMsg) : WHS :=
  if m.ty = MsgPreVote then st
  else if m.ty = MsgApp ∨ m.ty = MsgHeartbeat ∨ m.ty = MsgSnap then
    { st with term := m.term, vote := W64 0, lead := m.frm }
  else { st with term := m.term, vote := W64 0, lead := W64 0 }

/-- `handleHeartbeat(m, term)`: answered at the witness's term `term` (the stored state's, or
the one a newer-term heartbeat raised the state being built to: fork `9ed005d46`). -/
def wHeartbeat (id : w64) (term : w64) (m : WMsg) : WResp :=
  (respM MsgHeartbeatResp m.frm id term (W64 0) false, m.ctx)

/-- `handleAppendNoUpdate` against `σ` (`w.state`): the request's entry of the stored
`(term, subterm)` is acknowledged at its own index; one below the stored pair, at the stored
index; otherwise not handled (`false`): the state must be written. -/
def wAppendNoUpdate (id : w64) (σ : WHS) (m : WMsg) : WResp × Bool :=
  if m.lt = σ.lt ∧ m.ls = σ.ls then
    ((respM MsgAppResp m.frm id σ.term m.li false, []), true)
  else if ltPair m.lt m.ls σ.lt σ.ls then
    ((respM MsgAppResp m.frm id σ.term σ.li false, []), true)
  else ((respM MsgAppResp m.frm id σ.term (W64 0) false, []), false)

/-- `handleAppend`: answered without a write as `wAppendNoUpdate` against `σ`; else the state
`st` takes the request's entry and replication sets, and the answer acknowledges its index at
`st`'s term. -/
def wAppend (id : w64) (σ st : WHS) (m : WMsg) : WHS × WResp :=
  let r := wAppendNoUpdate id σ m
  if r.2 then (st, r.1)
  else
    let st' := { st with lt := m.lt, ls := m.ls, li := m.li, rs := m.rs0, rsOut := m.rs1 }
    (st', (respM MsgAppResp m.frm id st'.term st'.li false, []))

/-- The responders of the tally `votes` among the replication set `rs`, counted over `rs`
(`handleVote`'s `votesInSet`). -/
def votesInSet (rs : List w64) (votes : GMap w64 Bool) : Nat :=
  (rs.filter (fun x => (votes !! x).isSome)).length

/-- `handleVote` on the state `st`: it may vote for the candidate (it voted for it, or for nobody
knowing no leader, or a pre-vote of a later term), and grants unless the candidate's last
`(term, subterm)` is below its own, or equal with a responder outside the stored replication
set. A granted vote (not a pre-vote) is recorded. A rejection carries `st`'s term, a grant the
request's. -/
def wVote (id : w64) (st : WHS) (m : WMsg) : WHS × WResp :=
  let rty := if m.ty = MsgPreVote then MsgPreVoteResp else MsgVoteResp
  let canVote := st.vote = m.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨
    (m.ty = MsgPreVote ∧ uint.Z st.term < uint.Z m.term)
  let reject : Bool :=
    if canVote then
      if ltPair m.lt m.ls st.lt st.ls then true
      else if m.lt = st.lt ∧ m.ls = st.ls then
        decide (votesInSet st.rs m.votes ≠ GMap.size m.votes)
      else false
    else true
  let st' := if m.ty = MsgVote ∧ reject = false then { st with vote := m.frm } else st
  (st', (respM rty m.frm id (if reject then st'.term else m.term) (W64 0) reject, []))

/-- `processNoUpdate` against the state `σ` (`w.state`; `healthy`: the last storage access did
not fail): `some r` when handled without the storage (a heartbeat while unhealthy gets no
answer; an older term the `wOlder` answer; an append of `σ`'s term answered by
`wAppendNoUpdate`), `none` otherwise. -/
def wNoUpdate (id : w64) (cq pv healthy : Bool) (σ : WHS) (m : WMsg) : Option (Option WResp) :=
  if !healthy && decide (m.ty = MsgHeartbeat) then some none
  else if uint.Z m.term < uint.Z σ.term then some (wOlder id cq pv σ m)
  else if m.term = σ.term ∧ m.ty = MsgApp then
    let r := wAppendNoUpdate id σ m
    if r.2 then some (some r.1) else none
  else none

/-- One round of `Process`'s loop on the state `σ` just read: a heartbeat of `σ`'s term is
answered at it without a write (`none` for the state); a request `wNoUpdate` handles likewise; else the
new state (`wNewer` for a newer term, then the handler) to be written, with the answer. -/
def wStep (id : w64) (cq pv : Bool) (σ : WHS) (m : WMsg) : Option WHS × Option WResp :=
  if m.ty = MsgHeartbeat ∧ m.term = σ.term then (none, some (wHeartbeat id σ.term m))
  else match wNoUpdate id cq pv true σ m with
  | some r => (none, r)
  | none =>
    let st := if uint.Z σ.term < uint.Z m.term then wNewer σ m else σ
    if m.ty = MsgHeartbeat then (some st, some (wHeartbeat id st.term m))
    else if m.ty = MsgApp then
      let r := wAppend id σ st m
      (some r.1, some r.2)
    else
      let r := wVote id st m
      (some r.1, some r.2)

end model

end EtcdGrove
end Perennial
