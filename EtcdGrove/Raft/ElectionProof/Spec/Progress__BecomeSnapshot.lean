/-
Port of `election_proof/spec_Progress__BecomeSnapshot.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `pr.BecomeSnapshot(snapshoti)` moves a `Progress` into `StateSnapshot` and records
the pending snapshot index (`tracker.Progress.BecomeSnapshot.impl`,
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`):

    pr.ResetState(StateSnapshot)
    pr.PendingSnapshot = snapshoti
    pr.Next = snapshoti + 1
    pr.sentCommit = snapshoti

Like `BecomeReplicate`, it says nothing about votes, terms or roles, so the model does
not see it; the content of the triple is that `ownProgress`'s invariants survive -- in
particular `ProgressStateOk`, since `StateSnapshot` is one of the three legal states
(`InvTracker.lean`). -/
abbrev tracker.Progress.BecomeSnapshot.spec : Prop :=
  ∀ (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights) (snapshoti : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr pv iv }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"BecomeSnapshot"))
      (Val #snapshoti))
  {{ RET #(); ∃ pv' iv', ownProgress pr pv' iv' }}

end spec

end EtcdGrove
end Perennial
