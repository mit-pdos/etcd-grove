module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Conflict

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem any_false_of_idx {A : Type} (l : List A) (f : A → Bool) (n : Nat) (hn : l.length ≤ n)
    (h : ∀ j x, j < n → l[j]? = some x → f x = false) : l.any f = false := by
  rw [List.any_eq_false]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simpa using h j _ (by omega) (List.getElem?_eq_getElem hj)

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : StateTreemap GF]

theorem state.ConflictBatch.spec_holds : state.ConflictBatch.spec (GF := GF) := by
  intro s1 s2 dq1 dq2 b1 b2 hb1 hb2
  have hconf := state.Conflict.spec_holds (GF := GF)
  wp_start as ⟨H1, H2⟩
  unfold ownCmds
  icases H1 with ⟨%vs1, Hs1, %Hl1, #Hc1⟩
  icases H2 with ⟨%vs2, Hs2, %Hl2, #Hc2⟩
  wp_auto
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hs1
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave HI : (∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s1.len ∧
        ∀ i' (g : WCmd), i' < sint.nat i → b1[i']? = some g → b2.any (conflict g) = false⌝ :
      IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by decide, by word, ?_⟩
    intro i' g hi'; have : sint.nat (W64 0) = 0 := rfl; omega
  wp_for HI
  wp_if_destruct
  · -- outer body
    have hi : sint.Z i < sint.Z s1.len := by simpa using Hif
    list_elem b1 (sint.nat i) as g
    list_elem vs1 (sint.nat i) as gv
    ihave HI2 : (∃ j : w64,
        "j" ∷ j_ptr ↦ j ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s2.len ∧
          ∀ j' (d : WCmd), j' < sint.nat j → b2[j']? = some d → conflict g d = false⌝ :
        IProp GF) $$ [j]
    · iexists W64 0
      iframe
      ipureintro
      refine ⟨by decide, by word, ?_⟩
      intro j' d hj'; have : sint.nat (W64 0) = 0 := rfl; omega
    ihave Hgc := BigSepL.bigSepL_lookup Hgv_lookup $$ Hc1
    icases Hgc with ⟨%g', %Hg', #Hgc⟩
    rw [Hg_lookup] at Hg'; cases Hg'
    wp_for HI2
    wp_if_destruct
    · -- inner body
      have hj : sint.Z j < sint.Z s2.len := by simpa using Hif
      list_elem b2 (sint.nat j) as d
      list_elem vs2 (sint.nat j) as dv
      ihave Hdc := BigSepL.bigSepL_lookup Hdv_lookup $$ Hc2
      icases Hdc with ⟨%d', %Hd', #Hdc⟩
      rw [Hd_lookup] at Hd'; cases Hd'
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hi⟩)]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, hj⟩)]
      icases ownSlice_elem_acc (sint.Z i) gv s1 _ vs1 Hi.1 (by simpa using Hgv_lookup) $$ Hs1
        with ⟨Hg, Hs1⟩
      icases ownSlice_elem_acc (sint.Z j) dv s2 _ vs2 Hj.1 (by simpa using Hdv_lookup) $$ Hs2
        with ⟨Hd, Hs2⟩
      wp_apply hconf _ _ _ _ gv dv g d (hb1 g (List.mem_of_getElem? Hg_lookup))
        (hb2 d (List.mem_of_getElem? Hd_lookup)) $$ [$Hg $Hd $Hgc $Hdc] as ⟨Hg, Hd⟩
      ihave Hs1 := Hs1 $$ Hg
      ihave Hs2 := Hs2 $$ Hd
      rw [show (sint.Z i).toNat = sint.nat i from rfl, list_set_lookup_self _ _ _ Hgv_lookup,
        show (sint.Z j).toNat = sint.nat j from rfl, list_set_lookup_self _ _ _ Hdv_lookup]
      cases Hif : conflict g d
      · wp_auto
        wp_for_post
        iframe
        iexists j + W64 1
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro j' d' hj' hd'
        by_cases hjj : j' < sint.nat j
        · exact Hj.2.2 j' d' hjj hd'
        · have : j' = sint.nat j := by word
          subst this; rw [Hd_lookup] at hd'; cases hd'; exact Hif
      · -- `Conflict` was true: return
        wp_auto
        wp_for_post
        wp_for_post
        rw [show conflictBatch b1 b2 = true by
          unfold conflictBatch
          rw [List.any_eq_true]
          refine ⟨g, List.mem_of_getElem? Hg_lookup, ?_⟩
          rw [List.any_eq_true]
          exact ⟨d, List.mem_of_getElem? Hd_lookup, Hif⟩]
        iapply HΦ
        isplitl [Hs1]
        · iexists vs1; iframe Hs1; isplitr
          · ipureintro; exact Hl1
          · iexact Hc1
        · iexists vs2; iframe Hs2; isplitr
          · ipureintro; exact Hl2
          · iexact Hc2
    · -- inner exit: no conflict with `g`
      have hj : sint.Z s2.len ≤ sint.Z j := by simpa using Hif
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro i' g' hi' hg'
      by_cases hii : i' < sint.nat i
      · exact Hi.2.2 i' g' hii hg'
      · have : i' = sint.nat i := by word
        subst this; rw [Hg_lookup] at hg'; cases hg'
        exact any_false_of_idx b2 _ (sint.nat j) (by rw [← Hl2]; word) Hj.2.2
  · -- outer exit: no conflict
    have hi : sint.Z s1.len ≤ sint.Z i := by simpa using Hif
    rw [show conflictBatch b1 b2 = false by
      unfold conflictBatch
      exact any_false_of_idx b1 _ (sint.nat i) (by rw [← Hl1]; word) Hi.2.2]
    iapply HΦ
    isplitl [Hs1]
    · iexists vs1; iframe Hs1; isplitr
      · ipureintro; exact Hl1
      · iexact Hc1
    · iexists vs2; iframe Hs2; isplitr
      · ipureintro; exact Hl2
      · iexact Hc2

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
