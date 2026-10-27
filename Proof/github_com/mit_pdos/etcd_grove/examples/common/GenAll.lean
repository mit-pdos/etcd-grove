/- Lean-first (no Rocq counterpart). The proof of `genAll`: the loop appending `Gen()`'s. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.GenAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem GenAll.wp_proof (wp_Gen : Gen.spec (GF := GF) (hG := hG)) :
    GenAll.spec (GF := GF) (hG := hG) := by
  intro n ksl ks hn hk0 hk63
  wp_start as #Hk
  (try wp_auto)
  ihave HI : (∃ (j : w64) (sl : GoSlice) (ps : List wkv),
      "i" ∷ i_ptr ↦ j ∗ "all" ∷ all_ptr ↦ sl ∗ "Hs" ∷ sl ↦* ps ∗
      "Hcap" ∷ ownSliceCap wkv sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n ∧ ps.length = sint.nat j ∧
        ∀ p ∈ ps, GenKv ks p⌝ : IProp GF) $$ [i all]
  · iexists W64 0, slice.nil, []
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by word, by word, rfl, fun _ h => by simp at h⟩
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_Gen ksl ks hk0 hk63) as %p %Hp
    · iframe #
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

end common
end EtcdGrove
end Perennial
