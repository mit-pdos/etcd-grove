/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

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
  -- (raft-final, 2026-10-29, U9: in every cluster; until then outside the cluster's no-transfer
  -- mode, `RaftNames.reNoXfer = false`, D21 M2r)
  -- (2026-11-09, Q8 stage 0 of `notes/trace-validation-plan.md`) an untraced node: its trace
  -- hooks see a nil logger (`TraceLoggerOkS`); stage 1 replaces this premise by the traced
  -- capability (`trCapB s.gh.tr …`, `TracedHooksDraft.lean`)
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"TransferLeader")) (Val #transferee))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs }}

end spec

end EtcdGrove
end Perennial
