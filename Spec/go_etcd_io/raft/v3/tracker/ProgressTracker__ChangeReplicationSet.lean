/-
`(*ProgressTracker).ChangeReplicationSet` (raft#168, `tracker/tracker.go`; 2026-10-19, witness
support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

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

/-- `p.ChangeReplicationSet()` with a witness-free epoch: no half has an excluded voter to swap,
so nothing changes and it returns `false` (`stepLeader`'s check-quorum then starts no
subterm). -/
abbrev tracker.ProgressTracker.ChangeReplicationSet.spec : Prop :=
  ∀ (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownEpochNW tv.Epoch' }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"ChangeReplicationSet")) (Val #()))
  {{ RET #false; trk ↦{dq} tv }}

end spec

end EtcdGrove
end Perennial
