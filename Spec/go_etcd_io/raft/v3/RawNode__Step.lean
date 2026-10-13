/- Lean-first (no Rocq counterpart).

## `RawNode.Step` (rawnode.go:118), a message from the network

`Step(m)` drops a local message that does not come from a local target
(`ErrStepLocalMsg`) and a response from a node the tracker does not know
(`ErrStepPeerNotFound`); otherwise it is `rn.raft.Step(m)`.

Specified for the messages of replication and leader election (`NetMsgOk`): `MsgApp`,
`MsgAppResp`, `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`, `MsgHeartbeatResp`, and
(2026-10-13) of read-index: `MsgReadIndex`, `MsgReadIndexResp` -- not pre-vote (an
optimization), snapshots (log compaction, also an optimization) or the leader-transfer
messages -- with what the transport and the peers guarantee of them, which `raft.Step`
takes as premises (`Spec/raft__Step.lean`): addressed to this node, a nonzero term and
sender, and not from the node itself for a leader's `MsgApp`/`MsgHeartbeat`/
`MsgReadIndexResp`, a heartbeat response or a rejecting `MsgAppResp`. A `MsgReadIndex` is
a follower's forwarded request (or a local one, `node.ReadIndex`'s): unstamped (`Term =
0`), from and to anyone, and only in a configuration of more than one voter (`raft.Step`'s
premise: `IsSingleton`'s immediate answer is out of scope); it carries one read credit
(`rdCred`, `Hcred`), which `Ready` handed out with it. The message was legitimately sent
(`isMessage` of its abstraction) and its `Entries` are read-only but for the slice's
capacity, owned: `raftLog.maybeAppend` may adopt the slice. As a message the transport
delivers, it is the receiver's own copy. Its `Context` is not the leader-transfer marker;
until 2026-10-13 it was also empty on a heartbeat response (a read-index position is now
what `isMessage` says it is).

The client sees only the term, which moves up to at most the message's (`TermStep`).
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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The message types `RawNode.Step` is specified for: replication, leader election and
(2026-10-13) read-index. -/
def netStepTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
   MsgReadIndex, MsgReadIndexResp]

/-- A message from the network, as the transport and the peers deliver it to node `id`
(see the file header): but for a `MsgReadIndex` (unstamped, 2026-10-13), addressed to
`id`, of a nonzero term, from a nonzero sender. -/
def NetMsgOk [FfiSyntax] (id : w64) (m : raftpb.Message) : Prop :=
  m.Type' ∈ netStepTypes ∧
  (m.Type' ≠ MsgReadIndex → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0) ∧
  (m.Type' = MsgReadIndex → m.Term' = W64 0) ∧
  (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgHeartbeatResp ∨
     m.Type' = MsgReadIndexResp → m.From' ≠ id) ∧
  (m.Type' = MsgAppResp → m.Reject' = true → m.From' ≠ id)

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hents" ∷ m.Entries' ↦*□ ents ∗
      "Hents_cap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
      -- the `Context`: not the leader-transfer marker
      "#Hctx" ∷ m.Context' ↦*□ ctx ∗
      "%Hctx_ok" ∷ ⌜ctx ≠ campaignTransfer⌝ ∗
      "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m ents ctx)) ∗
      -- (2026-10-13) a read-index request's read credit
      "Hcred" ∷ rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Step")) (Val #m))
  {{ (err : GoInterface) (t : w64), RET #err;
      "Hrn" ∷ ownRawNode γ rn id { rs with term := t } ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧
               uint.Z t ≤ max (uint.Z rs.term) (uint.Z m.Term')⌝ }}

end spec

end EtcdGrove
end Perennial
