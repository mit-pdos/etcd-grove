/- Lean-first (no Rocq counterpart). The proof of `genAll`: the loop appending `Gen()`'s. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.genAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.cachekv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

theorem genAll.wp_proof (wp_Gen : Gen.spec (GF := GF) (hG := hG)) :
    genAll.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start as _
  (try wp_auto)
  ihave HI : (∃ (j : w64) (sl : GoSlice) (ps : List ckv),
      "i" ∷ i_ptr ↦ j ∗ "all" ∷ all_ptr ↦ sl ∗ "Hs" ∷ sl ↦* ps ∗
      "Hcap" ∷ ownSliceCap ckv sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n ∧ ps.length = sint.nat j ∧
        ∀ p ∈ ps, GenKv p⌝ : IProp GF) $$ [i all]
  · iexists W64 0, slice.nil, []
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by word, by word, rfl, fun _ h => by simp at h⟩
  wp_for HI
  wp_if_destruct
  · wp_apply wp_Gen as %p %Hp
    wp_apply wp_slice_literal (l := [p])
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, _⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hl1] as %sl' ⟨Hs, Hcap, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, sl', ps ++ [p]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp only [List.length_append, List.length_singleton, Hj.2.2.1]; word, ?_⟩
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact Hj.2.2.2 q hq
    · exact Hp
  · (try wp_auto)
    iapply HΦ
    iexists ps
    iframe
    ipureintro
    refine ⟨by rw [Hj.2.2.1]; word, Hj.2.2.2⟩

end proof

end cachekv
end EtcdGrove
end Perennial
