/-
`fieldpath.PathElementSet.Equals`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
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

theorem fieldpath.PathElementSet.Equals.wp_proof
    (h_PathElement_Equals : fieldpath.PathElement.Equals.spec (GF := GF)) :
    fieldpath.PathElementSet.Equals.spec (GF := GF) := fun l l2 dq dq2 A B => by
  wp_start as ⟨Hs, Hs2⟩
  unfold isPESet isPESetV
  icases Hs with ⟨%v, Hl, %es, %xs, Hm, #Hx, %h⟩
  icases Hs2 with ⟨%v2, Hl2, %es2, %ys, Hm2, #Hy, %h2⟩
  icases fpA.peset_members_acc l v dq $$ Hl with ⟨Hf, Hback⟩
  icases fpA.peset_members_acc l2 v2 dq2 $$ Hl2 with ⟨Hf2, Hback2⟩
  ihave %hwx := fpL.isPEL_wf _ _ $$ Hx
  ihave %hwy := fpL.isPEL_wf _ _ $$ Hy
  ihave %hlx := fpL.isPEL_length _ _ $$ Hx
  ihave %hly := fpL.isPEL_length _ _ $$ Hy
  ihave %hsx := ownSlice_len $$ Hm
  ihave %hsy := ownSlice_len $$ Hm2
  have hAB : A = B ↔ xs = ys := by
    rw [← h.2, ← h2.2]
    constructor
    · intro hab
      exact PE_sorted_ext_law_holds xs ys hwx hwy h.1 h2.1
        (fun x => by rw [← FSet.mem_ofList', ← FSet.mem_ofList', hab])
    · rintro rfl; rfl
  wp_auto
  wp_if_destruct
  · have Hleq := Hif
    have hlen : xs.length = ys.length := by
      have e1 := hsx.1; have e2 := hsy.1
      rw [Hif] at e1; rw [← hlx, ← hly, e1, e2]
    ihave HI : (∃ (i kv : w64), "i" ∷ i_ptr ↦ i ∗ "k" ∷ k_ptr ↦ kv ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.members'.len ∧
          ∀ j : Nat, j < (sint.Z i).toNat → xs[j]? = ys[j]?⌝ : IProp GF) $$ [i k]
    · iexists (W64 0), _; iframe; ipureintro
      refine ⟨by decide, hsx.2, ?_⟩
      intro j hj; simp at hj
    wp_for HI
    wp_if_destruct
    · have hb2 : sint.Z i < sint.Z v2.members'.len := by rw [← Hleq]; exact Hif
      have hix := fpA.idx_lt i _ _ hsx.1 Hi.1 Hif
      have hix2 := fpA.idx_lt i _ _ hsy.1 Hi.1 hb2
      list_elem es (sint.Z i).toNat as ea
      list_elem es2 (sint.Z i).toNat as eb
      simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v.members' (sint.Z i) es dq ea Hi.1) $$ [$Hm] as Hm
      · ipureintro; exact Hea_lookup
      simp only [Hi.1, hb2, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v2.members' (sint.Z i) es2 dq2 eb Hi.1) $$ [$Hm2] as Hm2
      · ipureintro; exact Heb_lookup
      simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
      wp_pures
      wp_method_call; wp_call
      wp_apply (wp_load_slice_index v.members' (sint.Z i) es dq ea Hi.1) $$ [$Hm] as Hm
      · ipureintro; exact Hea_lookup
      ihave ⟨%xa, %hxa, Ha⟩ := fpL.isPEL_lookup es xs _ ea Hea_lookup $$ Hx
      ihave ⟨%yb, %hyb, Hb⟩ := fpL.isPEL_lookup es2 ys _ eb Heb_lookup $$ Hy
      wp_apply (h_PathElement_Equals ea eb xa yb) $$ [$Ha $Hb] as %r %hr
      cases r
      · wp_auto
        wp_for_post
        iapply HΦ
        isplitl [Hf Hback Hm]
        · iexists v; isplitl [Hf Hback]
          · iapply Hback; iexact Hf
          iexists es, xs; iframe; isplit; iexact Hx; ipureintro; exact h
        isplitl [Hf2 Hback2 Hm2]
        · iexists v2; isplitl [Hf2 Hback2]
          · iapply Hback2; iexact Hf2
          iexists es2, ys; iframe; isplit; iexact Hy; ipureintro; exact h2
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        rw [hAB]; rintro rfl
        rw [hxa] at hyb; cases hyb
        simp at hr
      · wp_auto
        wp_for_post
        iframe
        iexists (i + W64 1), i
        iframe
        ipureintro
        have hxy : xa = yb := hr.1 rfl
        refine ⟨by word, by word, ?_⟩
        intro j hj
        rcases Nat.lt_or_ge j (sint.Z i).toNat with hj' | hj'
        · exact Hi.2.2 j hj'
        · have : j = (sint.Z i).toNat := by
            have : (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1 := by word
            omega
          subst this; rw [hxa, hyb, hxy]
    · wp_end
      isplitl [Hf Hback Hm]
      · iexists v; isplitl [Hf Hback]
        · iapply Hback; iexact Hf
        iexists es, xs; iframe; isplit; iexact Hx; ipureintro; exact h
      isplitl [Hf2 Hback2 Hm2]
      · iexists v2; isplitl [Hf2 Hback2]
        · iapply Hback2; iexact Hf2
        iexists es2, ys; iframe; isplit; iexact Hy; ipureintro; exact h2
      ipureintro
      simp only [_root_.true_iff]
      rw [hAB]
      have hle := fpA.idx_le i _ _ hsx.1 Hi.2.1
      have hge : xs.length ≤ (sint.Z i).toNat := by
        have := hsx.1; rw [hlx] at this; rw [this]; simp only [sint.nat, sint.Z] at Hif ⊢; omega
      apply List.ext_getElem? ; intro j
      rcases Nat.lt_or_ge j (sint.Z i).toNat with hj | hj
      · exact Hi.2.2 j hj
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  wp_end
  isplitl [Hf Hback Hm]
  · iexists v; isplitl [Hf Hback]
    · iapply Hback; iexact Hf
    iexists es, xs; iframe; isplit; iexact Hx; ipureintro; exact h
  isplitl [Hf2 Hback2 Hm2]
  · iexists v2; isplitl [Hf2 Hback2]
    · iapply Hback2; iexact Hf2
    iexists es2, ys; iframe; isplit; iexact Hy; ipureintro; exact h2
  ipureintro
  simp only [Bool.false_eq_true, false_iff]
  rw [hAB]; rintro rfl
  apply Hif
  have e1 := hsx.1; have e2 := hsy.1
  rw [← hlx, e1] at hly
  rw [hly] at e2
  simp only [sint.nat] at e2
  apply BitVec.eq_of_toInt_eq
  have := hsx.2; have := hsy.2
  simp only [sint.Z] at *
  omega

end proof

end smd
end EtcdGrove
end Perennial
