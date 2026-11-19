/-
`fieldpath.PathElementSet.Iterate`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Iterate
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.PathElementSet.Iterate.wp_proof :
    fieldpath.PathElementSet.Iterate.spec (GF := GF) := fun l dq S f I => by
  wp_start as ⟨Hs, HI0, #Hf⟩
  unfold isPESet isPESetV
  icases Hs with ⟨%v, Hl, %es, %xs, Hm, #Hx, %h⟩
  icases fpA.peset_members_acc l v dq $$ Hl with ⟨Hfl, Hback⟩
  ihave %hwx := fpL.isPEL_wf _ _ $$ Hx
  ihave %hlx := fpL.isPEL_length _ _ $$ Hx
  ihave %hsx := ownSlice_len $$ Hm
  have hnd := fpA.sorted_nodup xs hwx h.1
  wp_auto
  ihave HI : (∃ (i : w64) (pv : fieldpath.PathElement), "i" ∷ i_ptr ↦ i ∗ "pe" ∷ pe_ptr ↦ pv ∗
      "HIi" ∷ I (xs.take (sint.Z i).toNat) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.members'.len⌝ : IProp GF) $$ [i pe HI0]
  · iexists (W64 0), _; iframe; ipureintro; exact ⟨by decide, hsx.2⟩
  wp_for HI
  wp_if_destruct
  · have hix := fpA.idx_lt i _ _ hsx.1 Hi.1 Hif
    list_elem es (sint.Z i).toNat as ea
    simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index v.members' (sint.Z i) es dq ea Hi.1) $$ [$Hm] as Hm
    · ipureintro; exact Hea_lookup
    ihave ⟨%xa, %hxa, Ha⟩ := fpL.isPEL_lookup es xs _ ea Hea_lookup $$ Hx
    have hmem : xa ∈ S ∧ xa ∉ xs.take (sint.Z i).toNat := by
      refine ⟨by rw [← h.2, FSet.mem_ofList']; exact List.mem_of_getElem? hxa, ?_⟩
      intro hm
      have hnd' := hnd
      rw [← List.take_append_drop ((sint.Z i).toNat) xs] at hnd'
      have hd : xa ∈ xs.drop (sint.Z i).toNat := by
        rw [List.drop_eq_getElem_cons (by have := List.getElem?_eq_some_iff.1 hxa; exact this.1)]
        have := List.getElem?_eq_some_iff.1 hxa
        simp [this.2]
      exact (List.nodup_append.1 hnd').2.2 xa hm xa hd rfl
    wp_apply Hf $$ %(xs.take (sint.Z i).toNat) %ea %xa [] [HIi Ha] as HIi
    · ipureintro; exact hmem
    · iframe; iexact Ha
    wp_for_post
    iframe
    iexists (i + W64 1), ea
    have ht : xs.take (sint.Z (i + W64 1)).toNat = xs.take (sint.Z i).toNat ++ [xa] := by
      rw [show (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1 by word]
      rw [List.take_add_one, hxa]; rfl
    rw [ht]
    iframe
    ipureintro; constructor <;> word
  · have hle : xs.length ≤ (sint.Z i).toNat := by
      rw [← hlx, hsx.1]; simp only [sint.nat, sint.Z] at Hif ⊢; omega
    rw [List.take_of_length_le hle]
    wp_end
    isplitl [Hfl Hback Hm]
    · iexists v; isplitl [Hfl Hback]
      · iapply Hback; iexact Hfl
      iexists es, xs; iframe; isplit; iexact Hx; ipureintro; exact h
    iexists xs; iframe; ipureintro; exact ⟨hnd, h.2⟩

end proof

end smd
end EtcdGrove
end Perennial
