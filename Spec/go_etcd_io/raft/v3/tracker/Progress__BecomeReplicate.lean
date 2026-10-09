/-
Port of `election_proof/spec_Progress__BecomeReplicate.v` (feb5c73d4).

Lean notes: `progress_become_replicate` is `progressBecomeReplicate` (`Defs.lean`);
Rocq's `Progress__BecomeReplicateⁱᵐᵖˡ` is `tracker.Progress.BecomeReplicate.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `pr.BecomeReplicate()` moves a `Progress` into the replicating state
(`tracker.Progress.BecomeReplicate.impl`, Rocq new/code/go_etcd_io/raft/v3/tracker.v;
progress.go):

    pr.ResetState(StateReplicate)
    pr.Next = pr.Match + 1

It says nothing about votes, terms or roles, so the model does not see it. The new
record is `progressBecomeReplicate p` (`Defs.lean`); it leaves `matched` alone (Match
discipline, notes/raft-replication-model.md). `pr.Match + 1` is `uint64` arithmetic
and wraps, so it is `w64` addition. -/
abbrev tracker.Progress.BecomeReplicate.spec : Prop :=
  ∀ (pr : Loc) (p : Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"BecomeReplicate"))
      (Val #()))
  {{ RET #(); ownProgress pr (progressBecomeReplicate p) }}

end spec

end EtcdGrove
end Perennial
