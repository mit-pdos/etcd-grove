/- Lean-first (no Rocq counterpart). The proof of `addCand`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.addCand
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.histEq
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CandsLemmas

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

theorem addCand.wp_proof (wp_histEq : histEq.spec (GF := GF) (hG := hG)) :
    addCand.spec (GF := GF) (hG := hG) := by
  intro s si cs img unl pur
  wp_start as ⟨Hcs, #Himg⟩
  iunfold candsOwn at Hcs
  icases Hcs with ⟨%vs, Hs, Hcap, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := candsElems_length $$ Hel
  wp_auto
  ihave HI : (∃ (j : w64),
      "j" ∷ j_ptr ↦ j ∗ "cs" ∷ cs_ptr ↦ s ∗ "img" ∷ img_ptr ↦ si ∗ "unl" ∷ unl_ptr ↦ unl ∗
      "pur" ∷ pur_ptr ↦ pur ∗ "Hs" ∷ s ↦* vs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        ∀ i < sint.nat j, ∀ c, cs[i]? = some c → c.h ≠ img⌝ : IProp GF) $$ [j cs img unl pur Hs]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro i hi; rw [show sint.nat (W64 0) = 0 from rfl] at hi; omega
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z s.len
  · rw [if_pos (by simp [hlt])]
    have hil : sint.nat j < vs.length := by
      have : sint.nat j < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, hlt⟩
    icases candsElems_lookup vs cs (sint.nat j) v Hv $$ Hel with ⟨%c, %Hc, #Hcr⟩
    iunfold candRep at Hcr
    icases Hcr with ⟨%Hcf, #Hch⟩
    icases ownSlice_elem_acc (sint.Z j) v s (DFrac.own 1) vs Hj.1 (by simpa [sint.nat] using Hv) $$ Hs
      with ⟨Hv, Hsback⟩
    wp_auto
    repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_apply (wp_histEq v.h' si c.h img)
    · isplitr
      · iexact Hch
      · iexact Himg
    wp_if_destruct
    · iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_if_destruct
      all_goals iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      all_goals wp_if_destruct
      all_goals iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      all_goals
        wp_for_post
        ihave Hs := Hsback $$ Hv
        iapply HΦ
        iunfold candsOwn
        iexists _
        iframe
        rw [tAddCand_set c.h unl pur cs (sint.nat j) c Hc Hj.2.2 rfl]
        iapply candsElems_set
        isplitl []
        · iexact Hel
        iunfold candRep
        isplitr
        · ipureintro
          obtain ⟨h1, h2⟩ := Hcf
          simp only
          rw [← h1, ← h2]
          constructor <;> split <;> first | rfl | (exfalso; word)
        · iexact Hch
    · wp_for_post
      have hset : vs.set (sint.Z j).toNat v = vs := by
        apply List.ext_getElem?
        intro n
        rw [List.getElem?_set]
        split
        · rename_i hn
          subst hn
          exact Hv.symm
        · rfl
      ihave Hs := Hsback $$ Hv
      rw [hset]
      iframe
      iexists j + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro i hi c' hc'
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [hj1] at hi
      by_cases hij : i < sint.nat j
      · exact Hj.2.2 i hij c' hc'
      · have : i = sint.nat j := by omega
        subst this
        rw [Hc] at hc'
        cases hc'
        exact Hif
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hjn : sint.nat j = cs.length := by
      have : sint.nat j = sint.nat s.len := by word
      omega
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %csl ⟨Hcsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hcsl] as %s' ⟨Hs', Hcap', -⟩
    iapply HΦ
    rw [tAddCand_none img unl pur cs (fun c' hc' => by
      obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc'
      exact Hj.2.2 i (by omega) c' (by rw [← hci]; exact List.getElem?_eq_getElem hi))]
    iunfold candsOwn
    iexists _
    iframe
    iapply candsElems_snoc
    isplitl []
    · iexact Hel
    iunfold candRep
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    · iexact Himg

end proof

end etcd_wal
end EtcdGrove
end Perennial
