/- Lean-first (no Rocq counterpart). The proof of `freshOracle` (W4c U5). -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.freshOracle

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem freshOracle.wp_proof : freshOracle.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := cand) (W64 0)) as %cs0 ⟨Hcs0, Hcs0cap⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := walOp) (W64 0)) as %h0 ⟨Hh0, -⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  imod ownSlice_persist $$ Hh0 with #Hh0
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  wp_apply wp_slice_append $$ [$Hcs0 $Hcs0cap $Hcsl] as %cs1 ⟨Hcs1, Hcs1cap, -⟩
  wp_apply +noauto (wp_slice_make2 (V := walOp) (W64 0)) as %s0 ⟨Hs0, Hs0cap⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  imod ownSlice_persist $$ Hs0 with #Hs0
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := w64) (W64 0)) as %p0 ⟨Hp0, Hp0cap⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  imod ownSlice_persist $$ Hp0 with #Hp0
  wp_auto
  iapply HΦ
  iunfold oracleRep
  simp only [tFreshOracle]
  isplitr
  · ipureintro; simp [tHs0]; rfl
  isplitl [Hcs1 Hcs1cap]
  · iunfold candsOwn
    iexists _
    iframe
    iunfold candsElems
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %c %hi
    obtain ⟨h1, h2⟩ := hi
    rcases i with _ | i
    · simp only [List.nil_append, List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1 h2
      iunfold candRep
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iunfold opsRep
      iexists []
      isplitl []
      · iexact Hh0
      iapply opsElems_nil
    · simp at h1
  isplitl []
  · iunfold opsRep
    iexists []
    isplitl []
    · iexact Hs0
    iapply opsElems_nil
  iframe
  iexact Hp0

end proof

end etcd_wal
end EtcdGrove
end Perennial
