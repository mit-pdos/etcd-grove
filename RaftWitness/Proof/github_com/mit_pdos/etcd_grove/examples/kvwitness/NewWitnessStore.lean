/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/NewWitnessStore.lean`. Lean-first
(2026-10-20, witness support).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.NewWitnessStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- The zero state, frozen, then the mutex with its invariant. -/
theorem NewWitnessStore.wp_proof : NewWitnessStore.spec (GF := GF) (hG := hG) := by
  intro P
  wp_start as ⟨#Herr, HP⟩
  wp_pures
  wp_alloc hs as Hhs
  wp_auto
  -- `&WitnessHardState{State: &HardState{}}`: every cell nil, the slices nil, frozen
  imod whsOwn_of_struct «$v0_ptr» _ (zero_val raftpb.HardState) WHS.zero ⊤ $$ [«$v0» Hhs]
    with Hown
  · iframe
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    simp only [WHS.zero]
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    isplitr <;> iapply ownSlice_nil
  imod whsOwn_freeze $$ Hown with #Hro
  wp_alloc st as Hst
  iStructNamed Hst
  imod sync.init_Mutex (wStoreLock st P) ⊤ (st.[RWStore, go!"mu"]) $$ mu [state HP] with #Hmu
  · inext
    unfold wStoreLock
    iexists «$v0_ptr», WHS.zero
    iframe
    iframe #
  wp_auto
  iapply HΦ
  unfold isWStore
  iframe #

end proof

end kvwitness
end EtcdGrove
end Perennial
