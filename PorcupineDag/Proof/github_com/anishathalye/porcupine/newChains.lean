/- Lean-first (no Rocq counterpart). Proof of
`PorcupineDag/Spec/github_com/anishathalye/porcupine/newChains.lean`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newChains
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__computeFirstUnk
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__addToFrontier
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.NewChainsLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option maxHeartbeats 4000000 in
theorem newChains.wp_proof
    (wp_computeFirstUnk : chains.computeFirstUnk.spec (GF := GF) (hG := hG))
    (wp_addToFrontier : chains.addToFrontier.spec (GF := GF) (hG := hG)) :
    newChains.spec (GF := GF) (hG := hG) := by
  intro ohsl h cs cons hok hwf halloc
  wp_start as ⟨Hoh, #Hlin⟩
  iunfold ohistOwn at Hoh
  icases Hoh with ⟨%sls, Hsls, %Hslslen, Hcls⟩
  ihave %Hslen := ownSlice_len $$ Hsls
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := client) ohsl.len)
  · ipureintro; exact Hslen.2
  iintro %clsl ⟨Hcl, Hclcap⟩
  wp_auto
  revert i_ptr
  intro icnt_ptr
  irename : (i_ptr ↦ zero_val w64 : IProp GF) => ikey
  have hnc : sint.nat ohsl.len = cs.length := by rw [← Hslslen, Hslen.1]
  have hncZ : sint.Z ohsl.len = (cs.length : Int) := by
    rw [← hnc]; exact (Int.toNat_of_nonneg Hslen.2).symm
  -- the clients
  ihave IH1 : iprop(∃ (k nv kv : w64) (cv : GoSlice),
      "i" ∷ icnt_ptr ↦ k ∗ "ikey" ∷ i_ptr ↦ kv ∗ "c" ∷ c_ptr ↦ cv ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hcl" ∷ clsl ↦* ((List.range (sint.nat k)).map (clientAt sls) ++
        List.replicate (cs.length - sint.nat k) (zero_val client)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ cs.length ∧
        sint.Z nv = (((cs.take (sint.nat k)).map List.length).sum : Nat)⌝) $$ [i ikey c n Hcl]
  · iexists W64 0, W64 0, zero_val w64, zero_val GoSlice
    simp only [show sint.nat (W64 0) = 0 from rfl, List.range_zero, List.map_nil, List.nil_append,
      Nat.sub_zero, List.take_zero]
    rw [hnc]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp⟩
  wp_for IH1
  sorry

end proof

end porcupine
end EtcdGrove
end Perennial
