/-
`(*ProgressTracker).ResetReplicationSet` (raft#168, `tracker/tracker.go`; 2026-10-19, witness
support, `notes/raft-witness.md`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC

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

/-- `p.ResetReplicationSet(true)` (a new term's subterm 0): a fresh `Epoch` of subterm 0 whose
replication set in each half is the half's voters minus its witness; with no witness
(`ownTrackerC`'s configuration is witness-free) every voter, no witness and none excluded:
the tracker is the same but for its epoch, which is witness-free again (`ownEpochNW`). Only the
call with `true` is specified: with `false` (a configuration change) the subterm grows, which a
witness-free configuration never asks for (`switchToConfig` calls it only when a witness is
involved). -/
abbrev tracker.ProgressTracker.ResetReplicationSet.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"ResetReplicationSet")) (Val #true))
  {{ (e : Loc), RET #();
      trk ↦ { tv with Epoch' := e } ∗ ownTrackerC c { tv with Epoch' := e } t }}

end spec

end EtcdGrove
end Perennial
