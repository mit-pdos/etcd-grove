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

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`), taken as `Step` passes it
(`msgIn ml dqe`, the entry pointers owned for a `MsgProp` and read-only otherwise) and not given
back: a forwarded message (`MsgProp`, `MsgReadIndex`, `MsgTransferLeader`) gets `m.To =
new(r.lead)` and is frozen (`msgIn_to_msgOwn`) and queued by `send`; a `MsgApp`/`MsgSnap` goes
to `handleAppendEntries`/`handleSnapshot` whole. The `"Hctx"`/`"Hrents"`/`"Hents"` points-tos are
the message's state (`ents`, `cl`); the `MsgSnap` premise is pure, on the snapshot the message
holds (`sn = some sv`) and its `ConfState`'s lists (`scfg = sv.Metadata'.ConfState'.lists`; until
the retarget the read-only slices, `ownCSL`); "`Entries`/`Context` `nil`" is `ents = []`/`cl = []`.
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
def propForward (id lead : w64) (m : MessageM) (ents : List EntryM)
    (cl : List w8 := []) : Msg :=
  Msg.mkV .propose id lead (W64 0) m.Reject' m.Index' m.LogTerm' m.Commit' m.RejectHint'
    ents [] cl

/-- A read-index request forwarded to the leader `lead` (2026-10-12): `From` stamped if unset
(a twice-forwarded request keeps its requester), `Term` left at `0`. -/
def readForward (id lead : w64) (m : MessageM) (ents : List EntryM)
    (cl : List w8 := []) : Msg :=
  Msg.mkV .readIndex (if m.From' = W64 0 then id else m.From') lead (W64 0) m.Reject' m.Index'
    m.LogTerm' m.Commit' m.RejectHint' ents [] cl

/-- `FollowerStepResult` at the configuration `c` (2026-10-13, reconfiguration stage A2), with
the configuration `c'` the node is at afterwards: `c` itself, except after a `MsgSnap` that
`restore` installs, which moves it to the snapshot's (since 2026-10-14, stage A3; since B8 the
configuration its `ConfState`'s lists `scfg` denote, any; `SnapCfgOk`); `MsgTimeoutNow` campaigns
at `c` (`HupOkC`). -/
def FollowerStepResultC (c : CfgM) (scfg : CSLists) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sv : SnapshotM) (dropped : Bool) (s' : NState)
    (c' : CfgM) (cl : List w8 := []) : Prop :=
  (if m.Type' = MsgSnap then SnapCfgOk id c s sv scfg c'
   else c' = c) ∧
  (if m.Type' = MsgVoteResp then dropped = false ∧ s' = s
     else if m.Type' = MsgProp then
       if s.lead = W64 0 then dropped = true ∧ s' = s
       else dropped = false ∧ s' = sendMsgs s [propForward id s.lead m ents cl]
     else if m.Type' = MsgApp then
       dropped = false ∧ HandleAppResult id { s with lead := m.From' } m ents s'
     else if m.Type' = MsgHeartbeat then
       dropped = false ∧ s' = heartbeatResult id { s with lead := m.From' } m cl
     else if m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum then
       dropped = false ∧ s' = s
     else if m.Type' = MsgSnap then
       dropped = false ∧ HandleSnapResult id { s with lead := m.From' } m sv scfg s'
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
     else if m.Type' = MsgForgetLeader then dropped = false ∧ s' = { s with lead := W64 0 }
     else if m.Type' = MsgTransferLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus then
       dropped = false ∧ s' = s
     else if m.Type' = MsgTimeoutNow then
       -- (2026-10-17) the transfer's campaign makes no pre-candidate
       dropped = false ∧ HupOkC c id s s' ∧ (s'.role = .preCandidate → s'.role = s.role)
     else False)

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
  For `MsgVoteResp` the wand is discharged by the type. 

At any configuration since 2026-10-13 (reconfiguration stage A2): the struct at `c`
(`ownRaftPhysCV c c.voters`); `MsgTimeoutNow`'s campaign is at `c` (`FollowerStepResultC`).
A `MsgSnap` (since 2026-10-14, stage A3) at any `c`, joint or not, of a snapshot whose
`ConfState` holds the lists `scfg` (since B8 any well-formed ones, joint included, the node one
of its ids: `SnapScope`, `CSLists.Has`; in A3 non-joint with any voters; until then only at a non-joint
`c`, its voters `c.incoming`), after which the node is at the snapshot's configuration if
`restore` installed it (`SnapCfgOk`). (The statement on `ownRaftPhys`, `specS`, had no caller
and is gone.)
-/
abbrev stepFollower.spec : Prop :=
  ∀ (c : CfgM) (scfg : CSLists) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (rs : List Loc) (sv : SnapshotM) (cl : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum) ∨
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
     m.From' ≠ id ∧
     -- (2026-10-16, stage R8a) not a leader (`handleAppendEntries`'s premise: a leader's log only
     -- grows); `Step` dispatches here at a follower
     s.role ≠ .leader) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  -- (2026-10-13) a leader-transfer request is forwarded only unstamped (`send` panics on
  -- a stamped one; a stamped request reaches a follower of its term only without a leader:
  -- `raft.Step`'s premise), to another node; `MsgTimeoutNow` campaigns: the term does not
  -- wrap and `r.step` agrees with the role (`hup`'s premises)
  (m.Type' = MsgTransferLeader ∨ m.Type' = MsgTimeoutNow →
     (m.Type' = MsgTransferLeader → (s.lead = W64 0 ∨ (m.Term' = W64 0 ∧ s.lead ≠ id)) ∧
        ents = [] ∧ cl = [] ∧
        -- (2026-10-19, D21 M2r) only with leader transfer on (`NGhost.xf`)
        s.gh.xf = false) ∧
     (m.Type' = MsgTimeoutNow → uint.Z s.term + 1 < 2 ^ 64 ∧ NStateWf s ∧
       -- (D19i part 1) the floor at most `applied` (`hup`'s)
       uint.Z s.logst.fl ≤ uint.Z s.logst.applied)) →
  -- a snapshot (stage R4: pure, on the snapshot the message holds and its `ConfState`'s lists)
  (m.Type' = MsgSnap →
     sn = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
     SnapScopeIf id sv scfg ∧ s.role = .follower ∧ s.votes = ∅ ∧ m.From' ≠ id ∧
     -- (2026-10-19, D21 M3) outside the no-snapshot mode
     s.gh.ns = false) →
  -- (2026-10-22, D38a) a message forwarded to the leader has no responses (`send`'s premise)
  (m.Type' = MsgProp ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader → rs = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (stage R4) the message, as `Step` received it (its `Context` holding `cl`: what a
      -- forwarded proposal and the response to a heartbeat carry)
      "Hm" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
               ⟨m, ents, sn, cl, rs⟩ ∗
      -- (D22 S-b′3, 2026-10-20) a `MsgSnap`'s snapshot certified in the storage's registry
      -- (`handleSnapshot`'s; `tsSrc_ne` for any other type)
      "#Hcert" ∷ tsSrc s.logst.storage m.Type' sn }}
    (App (App (Val #(functions stepFollower [])) (Val #r)) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool) (c' : CfgM), RET #err;
      ownRaftPhysCV c' c'.voters r id s' ∗
      ⌜FollowerStepResultC c scfg id s m ents sv dropped s' c' cl⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
