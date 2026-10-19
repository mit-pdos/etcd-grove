/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ProgressTracker__OneLessThanQuorumInReplicationSet.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__OneLessThanQuorumInReplicationSet
public import Spec.go_etcd_io.raft.v3.tracker.Epoch__ReplicateToWitness

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

/-- No half replicates to a witness (`ReplicateToWitness` is `false, false`): `return nil`. -/
theorem tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.wp_proof
    (wp_ReplicateToWitness : tracker.Epoch.ReplicateToWitness.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec (GF := GF) (hG := hG) := by
  intro trk dq tv
  wp_start as ⟨Htrk, #He⟩
  wp_auto
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (A' := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hef, Htrkback⟩
  wp_auto
  ihave Htrk := Htrkback $$ Hef
  wp_apply wp_ReplicateToWitness tv.Epoch' $$ [$He]
  iapply HΦ; iframe Htrk

end proof

end EtcdGrove
end Perennial
