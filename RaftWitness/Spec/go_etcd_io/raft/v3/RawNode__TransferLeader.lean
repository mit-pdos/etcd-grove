/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A leader transfer to `transferee` (`MsgTransferLeader`, local, `From: transferee`): at a follower forwarded to the leader, at a leader recorded (`leadTransferee`) with a `MsgTimeoutNow` or an append to the transferee; the node predicate is kept (the term unchanged). -/
abbrev RawNode.TransferLeader.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (transferee : w64),
  -- (2026-10-19, D21 M2r) outside the cluster's no-snapshot mode, where leader transfer is off
  γ.reNoSnap = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"TransferLeader")) (Val #transferee))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs }}

end spec

end EtcdGrove
end Perennial
