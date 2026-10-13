/- Lean-first (no Rocq counterpart).

## `RawNode.Step` (rawnode.go:118), a message from the network

`Step(m)` drops a local message that does not come from a local target
(`ErrStepLocalMsg`) and a response from a node the tracker does not know
(`ErrStepPeerNotFound`); otherwise it is `rn.raft.Step(m)`.

Specified for the messages of replication and leader election (`NetMsgOk`): `MsgApp`,
`MsgAppResp`, `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`, `MsgHeartbeatResp`, and
(2026-10-13) of read-index: `MsgReadIndex`, `MsgReadIndexResp`; and (2026-10-13, for
`node.go`, whose `run` steps them all) leader transfer, `MsgTimeoutNow` and an unstamped
`MsgTransferLeader` (`TransferLeadership`'s), and the local `MsgForgetLeader`,
`MsgUnreachable`, `MsgSnapStatus` -- not pre-vote (an optimization), snapshots (log
compaction, also an optimization), nor a `MsgTransferLeader` a follower forwarded (stamped:
`raft.Step` takes it only of a receiver that is no follower with a leader at its term,
`RestMsgOk`, a fact of the receiver's state no message carries) -- with what the transport
and the peers guarantee of them, which `raft.Step` takes as premises
(`Spec/raft__Step.lean`): addressed to this node, a nonzero term and sender, and not from
the node itself for a leader's `MsgApp`/`MsgHeartbeat`/`MsgReadIndexResp`, a heartbeat
response or a rejecting `MsgAppResp`. The unstamped types (`UnstampedType`, `Term = 0`):
a `MsgReadIndex` is a follower's forwarded request (or a local one, `node.ReadIndex`'s),
from and to anyone, and only in a configuration of more than one voter (`raft.Step`'s
premise: `IsSingleton`'s immediate answer is out of scope); it carries one read credit
(`rdCred`, `Hcred`), which `Ready` handed out with it. A `MsgTransferLeader` carries no
entries and no context, as `TransferLeadership` builds it. A `MsgTimeoutNow` makes the node
campaign one term past its own or the message's: neither may be the last term
(`HtimeoutNow`). The message was legitimately sent (`isMessage` of its abstraction) and its
`Entries` are read-only but for the slice's capacity, owned: `raftLog.maybeAppend` may
adopt the slice. As a message the transport delivers, it is the receiver's own copy. Until
2026-10-13 its `Context` was not the leader-transfer marker (a transfer's vote request is
now an ordinary one, as for `raft.Step`) and empty on a heartbeat response (a read-index
position is now what `isMessage` says it is).

The client sees only the term, which moves up to at most the message's (`TermStep`), or
(2026-10-13) for a `MsgTimeoutNow` one past it or the node's.
Every type may come between `Ready` and `Advance`, as in the concurrent `node.go`. A
`MsgApp` may truncate the unstable entries a `Ready` handed out (`offsetInProgress`
moves back below the entry the queued `MsgStorageAppendResp` acknowledges), and a later
one may put that very entry back; the acknowledgement is then still right, because the
storage agrees with the log up to it by Log Matching (`StepsOk`, `stableOk_of_stored`,
`InvRawnode.lean`). Until 2026-10-10 the spec took a `MsgApp` only with no `Ready`
outstanding (`m.Type' = MsgApp → rs.steps = []`).

Lean notes: like `RawNode.Propose.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
-- `StepMsg`, `RestMsgOk` (2026-10-13)
public import Spec.go_etcd_io.raft.v3.raft__Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The message types `RawNode.Step` is specified for: replication, leader election,
(2026-10-13) read-index, leader transfer and the local reports. -/
def netStepTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
   MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow, MsgTransferLeader, MsgForgetLeader,
   MsgUnreachable, MsgSnapStatus]

/-- (2026-10-13) The types of `netStepTypes` that come unstamped (`Term = 0`): a read-index
request (forwarded or local), `TransferLeadership`'s request, and the local reports. -/
def UnstampedType (t : w32) : Prop :=
  t = MsgReadIndex ∨ t = MsgTransferLeader ∨ t = MsgForgetLeader ∨ t = MsgUnreachable ∨
    t = MsgSnapStatus

/-- A message from the network, as the transport and the peers deliver it to node `id`
(see the file header): but for the unstamped types (`Term = 0`, 2026-10-13), addressed to
`id`, of a nonzero term, from a nonzero sender; a transfer request with no entries and no
context. -/
def NetMsgOk [FfiSyntax] (id : w64) (m : raftpb.Message) : Prop :=
  m.Type' ∈ netStepTypes ∧
  (¬ UnstampedType m.Type' → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0) ∧
  (UnstampedType m.Type' → m.Term' = W64 0) ∧
  (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgHeartbeatResp ∨
     m.Type' = MsgReadIndexResp → m.From' ≠ id) ∧
  (m.Type' = MsgAppResp → m.Reject' = true → m.From' ≠ id) ∧
  (m.Type' = MsgTransferLeader → m.Entries' = slice.nil ∧ m.Context' = slice.nil)

theorem netStepTypes_nonneg {t : w32} (h : t ∈ netStepTypes) : 0 ≤ sint.Z t := by
  simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem netStepTypes_ne_prop {t : w32} (h : t ∈ netStepTypes) : t ≠ MsgProp := by
  intro he
  rw [he] at h
  simp [netStepTypes, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow, MsgTransferLeader,
    MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at h

theorem netStepTypes_stepMsg [FfiSyntax] {m : raftpb.Message} (h : m.Type' ∈ netStepTypes) :
    StepMsg m := by
  simp only [StepMsg, stepMsgTypes]
  simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

/-- What `raft.Step` takes of the types it was extended to last (`RestMsgOk`), from
`NetMsgOk` and the bound on the terms of a `MsgTimeoutNow`. -/
theorem NetMsgOk.restMsgOk [FfiSyntax] {id : w64} {s : NState} {m : raftpb.Message}
    (h : NetMsgOk id m)
    (ht : m.Type' = MsgTimeoutNow → uint.Z s.term + 1 < 2 ^ 64 ∧ uint.Z m.Term' + 1 < 2 ^ 64) :
    RestMsgOk s m := by
  obtain ⟨-, -, Hun, -, -, Htl⟩ := h
  refine ⟨fun h' => Hun ?_, ht, fun h' => ⟨(Htl h').1, (Htl h').2, fun hz => ?_⟩⟩
  · rcases h' with h' | h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inr (.inr (.inl h')))
    · exact .inr (.inr (.inr (.inr h')))
  · exact absurd (Hun (.inr (.inl h'))) hz

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev RawNode.Step.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8),
  NetMsgOk id m →
  -- (2026-10-13) a read-index request only with more than one voter (`raft.Step`'s)
  (m.Type' = MsgReadIndex → 1 < GMap.size γ.reCfg) →
  -- (2026-10-13) a `MsgTimeoutNow`'s campaign does not wrap the term (`raft.Step`'s)
  (m.Type' = MsgTimeoutNow → uint.Z rs.term + 1 < 2 ^ 64 ∧ uint.Z m.Term' + 1 < 2 ^ 64) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hents" ∷ m.Entries' ↦*□ ents ∗
      "Hents_cap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
      -- the `Context` (until 2026-10-13 not the leader-transfer marker)
      "#Hctx" ∷ m.Context' ↦*□ ctx ∗
      "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m ents ctx)) ∗
      -- (2026-10-13) a read-index request's read credit
      "Hcred" ∷ rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Step")) (Val #m))
  {{ (err : GoInterface) (t : w64), RET #err;
      "Hrn" ∷ ownRawNode γ rn id { rs with term := t } ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧
               uint.Z t ≤ max (uint.Z rs.term) (uint.Z m.Term') +
                 (if m.Type' = MsgTimeoutNow then 1 else 0)⌝ }}

end spec

end EtcdGrove
end Perennial
