/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/Epoch__HasWitness.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tracker.Epoch.HasWitness.wp_proof : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG) := by
  intro e em
  wp_start as #He
  icases ownEpoch_we e em $$ He with ⟨#Hw0, -, #Hw1, -⟩
  wp_auto
  wp_if_destruct
  · have h0 := Hif
    rw [show em.hasWit = !decide (em.rs1.wit = W64 0) by simp [EpochM.hasWit, h0]]
    iapply HΦ; itrivial
  · have h0 := Hif
    rw [show em.hasWit = true by simp [EpochM.hasWit]; exact Or.inl h0]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
