/- Port of election_proof/spec_stepFollower.v (feb5c73d4).

## `stepFollower`, for the message types in scope

`stepFollower.impl` (`Code/go_etcd_io/raft/v3.lean`; raft.go:1705) is a type
switch over `m.Type` with arms for `MsgProp`, `MsgApp`, `MsgHeartbeat`, `MsgSnap`,
`MsgTransferLeader`, `MsgForgetLeader`, `MsgTimeoutNow`, `MsgReadIndex` and
`MsgReadIndexResp`, then `return nil`. Specified for every type `Step` dispatches to it:

- `MsgVoteResp`, `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`, and (since 2026-10-04)
  `MsgPreVoteResp`: no arm; nothing read or written, `nil`.
- `MsgProp`: `r.lead == None` → `Infof` and `return ErrProposalDropped`, state
  unchanged. Otherwise `r.disableProposalForwarding` is read -- `false`, by
  `ownRaftPhys`'s `HpropForward` scope conjunct, so the second drop is dead -- then
  `m.To = r.lead; r.send(m)`: `SendOk`'s `MsgProp` clause (e) -- `Term` stays `0`,
  `From` is stamped `id` -- so the outbox grows by `absMsgFrom .propose (m with To :=
  lead) id 0 ents`, which is `propForward` below and `Step.propForward`'s message.
  (Until 2026-10-02 the forwarding arm was deferred behind a premise `lead = 0`.)
- `MsgApp`: `r.electionElapsed = 0` (not tracked), `r.lead = m.From`, then
  `handleAppendEntries` (`HandleAppResult` at `{ s with lead := m.From }`); `nil`.
- `MsgHeartbeat`: the same two stores, then `handleHeartbeat` (`heartbeatResult` at
  `{ s with lead := m.From }`); `nil`.
- `MsgSnap` (since 2026-10-02): the same two stores, then `handleSnapshot`
  (`HandleSnapResult` at `{ s with lead := m.From }`, for the snapshot `sv` that
  `m.Snapshot` points to); `nil`.

The role is never read: the triple holds for any `s`. (A caller reaching it through
`r.step` knows `s.role = .follower` from `NStateWf`.)

Lean notes:
* Rocq's `prop_forward` and `follower_step_result` are `propForward` and
  `FollowerStepResult` (a Prop-valued definition); `if decide (P) then … else …` is
  `if P then … else …`.
* The Rocq file also defines a tactic, `step_no_snap`, for a caller of
  `stepFollower`/`stepCandidate` with a message that is not a `MsgSnap`: it discharges
  the `"Hsnap"` premise's wand by its antecedent's falsity (some hypothesis `m.Type =
  c`, or a disjunction of such, with `c` not `MsgSnap`). A spec file states and does
  not prove, so it is not ported here (a proof introduces the antecedent and refutes it
  by rewriting and `decide`).
-/
module

-- read-index (2026-10-12): `addReadState`
public import Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
-- (2026-10-13) `HupOk`, for `MsgTimeoutNow`
public import Spec.go_etcd_io.raft.v3.raft__hup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The forwarded proposal as `send` queues it: `m` with `To := lead`, `From := id`
(stamped; `m.From = 0`), `Term = 0` (not stamped for `MsgProp`), the rest `m`'s. Field
for field what `Step.propForward` sends (`Msg.mk .propose id s.lead (W64 0) m.reject
m.index m.logterm m.commit m.rejecthint m.entries`). -/
def propForward (id lead : w64) (m : raftpb.Message) (ents : List raftpb.Entry)
    (cl : List w8 := []) : Msg :=
  Msg.mkV .propose id lead (W64 0) m.Reject' m.Index' m.LogTerm' m.Commit' m.RejectHint'
    ents [] cl

/-- A read-index request forwarded to the leader `lead` (2026-10-12): `From` stamped if unset
(a twice-forwarded request keeps its requester), `Term` left at `0`. -/
def readForward (id lead : w64) (m : raftpb.Message) (ents : List raftpb.Entry)
    (cl : List w8 := []) : Msg :=
  Msg.mkV .readIndex (if m.From' = W64 0 then id else m.From') lead (W64 0) m.Reject' m.Index'
    m.LogTerm' m.Commit' m.RejectHint' ents [] cl

/-- What `stepFollower` does with `m`, by type. `dropped` is whether it returned
`ErrProposalDropped` (the postcondition then says `err` is that global's value;
otherwise `err = nil`). -/
def FollowerStepResult (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8 := []) : Prop :=
  if m.Type' = MsgVoteResp then dropped = false ∧ s' = s
  else if m.Type' = MsgProp then
    if s.lead = W64 0 then dropped = true ∧ s' = s
    else dropped = false ∧ s' = sendMsgs s [propForward id s.lead m ents cl]
  else if m.Type' = MsgApp then
    dropped = false ∧ HandleAppResult id { s with lead := m.From' } m ents s'
  else if m.Type' = MsgHeartbeat then
    dropped = false ∧ s' = heartbeatResult id { s with lead := m.From' } m cl
  else if m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp then
    dropped = false ∧ s' = s
  else if m.Type' = MsgSnap then
    dropped = false ∧ HandleSnapResult id { s with lead := m.From' } m sv s'
  else if m.Type' = MsgPreVoteResp then dropped = false ∧ s' = s
  -- read-index (2026-10-12): a request goes to the leader, a response becomes a `ReadState`
  else if m.Type' = MsgReadIndex then
    dropped = false ∧
    (if s.lead = W64 0 then s' = s
     else s' = sendMsgs s [readForward id s.lead m ents cl])
  else if m.Type' = MsgReadIndexResp then
    dropped = false ∧
    (match ents with
     | [e] => s' = addReadState s m.Index' e.Data'
     | _ => s' = s)
  -- (2026-10-13) `ForgetLeader` clears the leader (the read-only option is `Safe`);
  -- a leader-transfer request is forwarded to the leader, or dropped without one, and
  -- carries nothing the model sees; the local reports have no arm; `MsgTimeoutNow`
  -- campaigns (`hup(campaignTransfer)`), with the voters `domSet s.progress` (`= cfg`,
  -- `ownRaftPhys_progress_dom`)
  else if m.Type' = MsgForgetLeader then dropped = false ∧ s' = { s with lead := W64 0 }
  else if m.Type' = MsgTransferLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus then
    dropped = false ∧ s' = s
  else if m.Type' = MsgTimeoutNow then dropped = false ∧ HupOk (domSet s.progress) id s s'
  else False

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Premises, by type:
- `MsgProp`: `From` unset or `id` (since 2026-10-06: `RawNode.Propose` stamps `From:
  r.id`) and `Term = 0` (a local proposal; `send` takes the first and its `MsgProp`
  clause the second) and `lead ≠ id` (`send`'s self-addressed `Panicf`) -- for the
  forwarding arm;
- `MsgApp`: `handleAppendEntries`'s premises, at `s` (`lead` does not enter them),
  `m.From ≠ id` among them since 2026-10-10 (and `handleSnapshot`'s for a `MsgSnap`);
- `MsgHeartbeat`: `handleHeartbeat`'s two -- `m.Commit` within the log (`commitTo`'s
  `Panicf`; the protocol fact `heartbeat_commit_le_last`) and `m.From ≠ id` (`send`'s
  self-addressed `Panicf`);
- `Hents`: the `Entries` slice for the two types that use it -- read-only for
  `send`/`maybeAppend`, with its capacity for `maybeAppend` (it may adopt the slice).
  For `MsgVoteResp` the wand is discharged by the type. -/
abbrev stepFollower.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (voters : List w64) (cl : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp) ∨
   m.Type' = MsgSnap ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)) →
  -- (2026-10-12) a read-index request is unstamped, and the leader is another node
  (m.Type' = MsgReadIndex → m.Term' = W64 0 ∧ s.lead ≠ id) →
  (m.Type' = MsgProp →
     (m.From' = W64 0 ∨ m.From' = id) ∧
     m.Term' = W64 0 ∧
     s.lead ≠ id) →
  (m.Type' = MsgApp →
     PlogWf (entryID.mk m.LogTerm' m.Index') ents ∧
     uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 ∧
     (let ls := s.logst
      let es := ls.sents ++ ls.uents
      uint.Z ls.committed ≤ uint.Z m.Index' →
      PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
      plogFindConflict ls.prev es ents = W64 0 ∨
      uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) ∧
     -- from another node (2026-10-10, `handleAppendEntries`'s premise)
     m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  -- (2026-10-13) a leader-transfer request is forwarded only unstamped (`send` panics on
  -- a stamped one; a stamped request reaches a follower of its term only without a leader:
  -- `raft.Step`'s premise), to another node; `MsgTimeoutNow` campaigns: the term does not
  -- wrap and `r.step` agrees with the role (`hup`'s premises)
  (m.Type' = MsgTransferLeader ∨ m.Type' = MsgTimeoutNow →
     (m.Type' = MsgTransferLeader → (s.lead = W64 0 ∨ (m.Term' = W64 0 ∧ s.lead ≠ id)) ∧
        m.Entries' = slice.nil ∧ m.Context' = slice.nil) ∧
     (m.Type' = MsgTimeoutNow → uint.Z s.term + 1 < 2 ^ 64 ∧ NStateWf s)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      -- the `Context` (2026-10-12): what a forwarded proposal and the response to a
      -- heartbeat carry
      "Hctx" ∷ (⌜m.Type' = MsgHeartbeat ∨ m.Type' = MsgProp ∨ m.Type' = MsgReadIndex⌝ -∗
                 m.Context' ↦*□ cl) ∗
      -- (2026-10-12) a read-index message's entries, read-only
      "Hrents" ∷ (⌜m.Type' = MsgReadIndex ∨ m.Type' = MsgReadIndexResp⌝ -∗
                  m.Entries' ↦*□ ents) ∗
      "Hsnap" ∷ (⌜m.Type' = MsgSnap⌝ -∗
                 ⌜SnapScope cfg sv voters ∧ s.role = .follower ∧
                   s.votes = ∅ ∧ id ∈ cfg ∧ m.From' ≠ id⌝ ∗
                 m.Snapshot' ↦□ sv ∗
                 sv.Metadata'.ConfState'.Voters' ↦*□ voters) ∗
      "Hents" ∷ (⌜m.Type' = MsgApp ∨ m.Type' = MsgProp⌝ -∗
                 m.Entries' ↦*□ ents ∗
                 ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)) }}
    (App (App (Val #(functions stepFollower [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhys cfg r id s' ∗
      ⌜FollowerStepResult id s m ents sv dropped s' cl⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
