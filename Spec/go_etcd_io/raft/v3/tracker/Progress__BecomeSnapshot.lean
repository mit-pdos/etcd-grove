/-
Port of election_proof/spec_Progress__BecomeSnapshot.v (feb5c73d4).

Lean notes:
* Rocq's `own_Progress pr p` with `p : progress.t` is `ownProgress pr p` with
  `p : Progress` (`Defs.lean`); `progress_become_snapshot` is `progressBecomeSnapshot`.
* The reference `Progress__BecomeSnapshotⁱᵐᵖˡ` is to the Lean generated code
  `tracker.Progress.BecomeSnapshot.impl`.
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

/-- `pr.BecomeSnapshot(snapshoti)` moves a `Progress` into `StateSnapshot` and records
the pending snapshot index (`tracker.Progress.BecomeSnapshot.impl`,
`Code/go_etcd_io/raft/v3/tracker.lean`):

    pr.ResetState(StateSnapshot)
    pr.PendingSnapshot = snapshoti
    pr.Next = snapshoti + 1
    pr.sentCommit = snapshoti

Like `BecomeReplicate`, it says nothing about votes, terms or roles, so the model does
not see it. The new record is `progressBecomeSnapshot p snapshoti` (`Defs.lean`);
`matched` is untouched (Match discipline, notes/raft-replication-model.md). -/
abbrev tracker.Progress.BecomeSnapshot.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (snapshoti : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"BecomeSnapshot"))
      (Val #snapshoti))
  {{ RET #(); ownProgress pr (progressBecomeSnapshot p snapshoti) }}

end spec

end EtcdGrove
end Perennial
