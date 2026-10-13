/-
Proof of `Spec/SnapshotMetadata__GetIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

theorem raftpb.SnapshotMetadata.GetIndex.wp_proof :
    raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG) := by
  intro md i
  wp_start as H
  icases H with (⟨%Hnull, %Hz⟩ | ⟨%p, %Hnn, #Hf, #Hp⟩)
  · subst Hnull Hz
    wp_auto
    iapply HΦ
    itrivial
  · have hd : decide (md = null) = false := decide_eq_false Hnn
    wp_auto
    simp only [hd, Bool.not_false]
    wp_auto
    iunfold optU64 at Hp
    by_cases hp : p = null
    · rw [ite_eq_left hp]
      icases Hp with %Hz
      subst hp
      (try wp_auto)
      rw [← Hz]
      iapply HΦ
      itrivial
    · rw [ite_eq_right hp]
      (try wp_auto)
      have hd' : decide (p = null) = false := decide_eq_false hp
      simp only [hd', Bool.not_false]
      wp_auto
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
