/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ProgressTracker__ChangeReplicationSet.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ChangeReplicationSet
public import Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- With no witness the epoch's `HasWitness()` is `false`: the early return. -/
theorem tracker.ProgressTracker.ChangeReplicationSet.wp_proof
    (wp_HasWitness : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG) := by
  intro trk dq tv
  wp_start as ⟨Htrk, #He⟩
  ihave #He' := He
  iunfold ownEpochNW at He'
  icases He' with ⟨%ev, #Hev, -⟩
  ihave %Hnn := typedPointsto_not_null $$ Hev
  wp_auto
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (A' := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hef, Htrkback⟩
  wp_auto
  ihave Htrk := Htrkback $$ Hef
  rw [decide_eq_false (by simpa using Hnn)]
  wp_auto
  wp_apply wp_HasWitness tv.Epoch' $$ [$He]
  iapply HΦ; iframe Htrk

end proof

end EtcdGrove
end Perennial
