/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/Epoch__ReplicateToWitness.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.Epoch__ReplicateToWitness

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

theorem tracker.Epoch.ReplicateToWitness.wp_proof :
    tracker.Epoch.ReplicateToWitness.spec (GF := GF) (hG := hG) := by
  intro e em
  wp_start as #He
  icases ownEpoch_we e em $$ He with ⟨#Hw0, #He0, #Hw1, #He1⟩
  wp_auto
  wp_if_destruct
  · have h0 := Hif
    rw [show em.rs0.rep = false by simp [RSM.rep, h0]]
    wp_if_destruct
    · have h1 := Hif
      rw [show em.rs1.rep = false by simp [RSM.rep, h1]]
      iapply HΦ; itrivial
    · have h1 := Hif
      rw [show em.rs1.rep = !decide (em.rs1.excl = em.rs1.wit) by simp [RSM.rep]; exact fun _ => h1]
      iapply HΦ; itrivial
  · have h0 := Hif
    rw [show em.rs0.rep = !decide (em.rs0.excl = em.rs0.wit) by simp [RSM.rep]; exact fun _ => h0]
    wp_if_destruct
    · have h1 := Hif
      rw [show em.rs1.rep = false by simp [RSM.rep, h1]]
      iapply HΦ; itrivial
    · have h1 := Hif
      rw [show em.rs1.rep = !decide (em.rs1.excl = em.rs1.wit) by simp [RSM.rep]; exact fun _ => h1]
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
