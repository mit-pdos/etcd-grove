module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.shows
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeItemRVs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item WEvent)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `shows`' test of a watch event. -/
def wevHit (key : GoString) (r : w64) (e : WEv) : Bool :=
  decide (e.t < 3) && decide (objKeyL e.o = key) && decide (e.o.ResourceVersion' = r)

/-- `shows`' test of a list item. -/
def itemHit (key : GoString) (r : w64) (o : Obj) : Bool :=
  decide (objKeyL o = key) && decide (o.ResourceVersion' = r)

theorem sint_lt3_iff (t : w64) (h : uint.nat t < 256) :
    sint.Z t < sint.Z (W64 3) ↔ uint.nat t < 3 := by
  word

theorem shows.wp_proof
    (wp_decodeWEvents : decodeWEvents.spec (GF := GF) (hG := hG))
    (wp_decodeItemRVs : decodeItemRVs.spec (GF := GF) (hG := hG)) :
    shows.spec (GF := GF) (hG := hG) := by
  intro x y key r
  wp_start as -
  wp_auto
  wp_if_destruct
  · -- a watch
    have hk5 : x.Kind' = W64 5 := by first | exact Hif | simpa using Hif
    wp_apply wp_decodeWEvents as %sl %ok Hd
    rcases hd : decWEventsL y.WEvents' with _ | all
    · isimp only [hd] at Hd
      icases Hd with %Hok
      subst Hok
      (try wp_auto)
      rw [show showsL x y key r = false by simp [showsL, hk5, hd]]
      iapply HΦ; itrivial
    isimp only [hd] at Hd
    icases Hd with ⟨%Hok, Hw⟩
    subst Hok
    imod wevsOwnM_persist _ _ $$ Hw with #Hw
    unfold wevsOwn
    icases Hw with ⟨%ws, #Hk, %He⟩
    ihave %Hl := ownSlice_len $$ Hk
    have hty : ∀ e ∈ all, e.t < 256 := fun e he =>
      decWEventsL_t y.WEvents'.length y.WEvents' (Nat.le_refl _) all hd e he
    (try wp_auto)
    cases hF : y.WFailed'
    case true =>
      (try wp_auto)
      rw [show showsL x y key r = false by simp [showsL, hk5, hd, hF]]
      iapply HΦ; itrivial
    (try wp_auto)
    ihave HI : (∃ (j : w64) (evv : WEvent),
        "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
          ∀ e ∈ (ws.map wevOf).take (sint.nat j), wevHit key r e = false⌝ : IProp GF) $$ [i ev]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, ?_⟩
      intro e he
      simp [show sint.nat (0#64 : w64) = 0 from rfl] at he
    irename : (in_ptr ↦ x : IProp GF) => Hin
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
        ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
      list_elem ws (sint.nat j) as w
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z j) ws _ w Hj.1 $$ [Hk] as -
      · isplit
        · iexact Hk
        · ipureintro; exact Hw_lookup
      have hl : (ws.map wevOf)[sint.nat j]? = some (wevOf w) := by simp [Hw_lookup]
      have hmem : wevOf w ∈ all := by
        rw [← He]; exact List.mem_of_getElem? hl
      have ht := hty _ hmem
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have htake : (ws.map wevOf).take (sint.nat j + 1) =
          (ws.map wevOf).take (sint.nat j) ++ [wevOf w] := by
        rw [List.take_add_one, hl]; rfl
      have h3iff := sint_lt3_iff w.Type' (by simpa only [wevOf] using ht)
      wp_if_destruct
      · have h3 : uint.nat w.Type' < 3 := h3iff.1 Hif
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_if_destruct
          · (try wp_auto)
            wp_for_post
            have hsh : ∀ k rr, k = objKeyL w.Obj' → rr = w.Obj'.ResourceVersion' →
                showsL x y k rr = true := by
              rintro k rr rfl rfl
              simp only [showsL, hk5, hd, hF, ↓reduceIte, Bool.false_eq_true]
              rw [List.any_eq_true]
              refine ⟨wevOf w, hmem, ?_⟩
              simp only [wevOf, Bool.and_eq_true, decide_eq_true_eq]
              simp [h3]
            rw [hsh _ _ (by simp [objKeyL]) rfl]
            iapply HΦ; itrivial
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, w
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hj1, htake]
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact Hj.2.2 e he
          · simp only [wevHit, wevOf, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            first | exact Or.inr Hif | exact Or.inr (decide_eq_false Hif)
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, w
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hj1, htake]
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact Hj.2.2 e he
          · simp only [wevHit, wevOf, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            exact Or.inl (Or.inr (by simpa [objKeyL] using Hif))
      · have h3 : ¬ uint.nat w.Type' < 3 := fun h => Hif (h3iff.2 h)
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, w
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, htake]
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact Hj.2.2 e he
        · simp only [wevHit, wevOf, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Or.inl (Or.inl (decide_eq_false h3))
    · have hge : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
      (try wp_auto)
      have hfull : (ws.map wevOf).take (sint.nat j) = ws.map wevOf :=
        List.take_of_length_le (by simp; word)
      rw [hfull, He] at Hj
      have hs : showsL x y key r = false := by
        simp only [showsL, hk5, hd, hF, ↓reduceIte, Bool.false_eq_true]
        rw [List.any_eq_false]
        intro e he
        have := Hj.2.2 e he
        simpa [wevHit] using this
      rw [hs]
      iapply HΦ; itrivial
  wp_if_destruct
  · -- a list
    have hk4 : x.Kind' = W64 4 := by first | exact Hif | simpa using Hif
    wp_apply wp_decodeItemRVs as %sl %ok Hd
    rcases hd : decItemRVsL y.Items' with _ | os
    · isimp only [hd] at Hd
      icases Hd with %Hok
      subst Hok
      (try wp_auto)
      rw [show showsL x y key r = false by simp [showsL, hk4, hd]]
      iapply HΦ; itrivial
    isimp only [hd] at Hd
    icases Hd with ⟨%Hok, Hw⟩
    subst Hok
    imod ownSlice_persist _ _ _ $$ Hw with #Hk
    ihave %Hl := ownSlice_len $$ Hk
    (try wp_auto)
    cases hE : decide (y.Err' = W64 0)
    case false =>
      (try wp_auto)
      have hE' : y.Err' ≠ W64 0 := by simpa using hE
      have h45 : (W64 4 : w64) ≠ W64 5 := by decide
      rw [show showsL x y key r = false by
        simp only [showsL, hk4, hd, hE', h45, ↓reduceIte, ne_eq, not_false_eq_true]]
      iapply HΦ; itrivial
    (try wp_auto)
    ihave HI : (∃ (j : w64) (itv : item),
        "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
          ∀ o ∈ os.take (sint.nat j), itemHit key r o = false⌝ : IProp GF) $$ [i it]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, ?_⟩
      intro e he
      simp [show sint.nat (0#64 : w64) = 0 from rfl] at he
    irename : (in_ptr ↦ x : IProp GF) => Hin
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
        ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
      have hjl : sint.nat j < os.length := by
        have := Hl.1; simp only [List.length_map] at this; word
      list_elem os (sint.nat j) as o
      have hl := Ho_lookup
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z j) _ _ (item.mk (objKeyL o) o false) Hj.1 $$ [Hk] as -
      · isplit
        · iexact Hk
        · ipureintro; simp [hl]
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have htake : os.take (sint.nat j + 1) = os.take (sint.nat j) ++ [o] := by
        rw [List.take_add_one, hl]; rfl
      have hmem : o ∈ os := List.mem_of_getElem? hl
      wp_if_destruct
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_for_post
          have hsh : ∀ k rr, k = objKeyL o →
              rr = o.ResourceVersion' → showsL x y k rr = true := by
            rintro k rr rfl rfl
            have hE' : y.Err' = W64 0 := by simpa using hE
            have h45 : (W64 4 : w64) ≠ W64 5 := by decide
            simp only [showsL, hk4, hd, hE', h45, ↓reduceIte, ne_eq, not_true_eq_false]
            rw [List.any_eq_true]
            exact ⟨_, hmem, by simp⟩
          rw [hsh _ _ (by simp [objKeyL]) rfl]
          iapply HΦ; itrivial
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hj1, htake]
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact Hj.2.2 e he
          · simp only [itemHit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            first | exact Or.inr Hif | exact Or.inr (decide_eq_false Hif)
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, htake]
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact Hj.2.2 e he
        · simp only [itemHit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Or.inl (by simpa [objKeyL] using Hif)
    · have hge : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
      (try wp_auto)
      have hfull : os.take (sint.nat j) = os := List.take_of_length_le (by
        have := Hl.1; simp only [List.length_map] at this; word)
      rw [hfull] at Hj
      have hs : showsL x y key r = false := by
        have hE' : y.Err' = W64 0 := by simpa using hE
        have h45 : (W64 4 : w64) ≠ W64 5 := by decide
        simp only [showsL, hk4, hd, hE', h45, ↓reduceIte, ne_eq, not_true_eq_false]
        rw [List.any_eq_false]
        intro o ho
        have := Hj.2.2 o ho
        simpa [itemHit] using this
      rw [hs]
      iapply HΦ; itrivial
  -- a get or a write
  have hk5 : x.Kind' ≠ W64 5 := by assumption
  have hk4 : x.Kind' ≠ W64 4 := by assumption
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_if_destruct
    · rw [show showsL x y x.Key' r = decide (y.RV' = r) by
        simp only [showsL, if_neg hk5, if_neg hk4, ne_eq, not_true_eq_false, ↓reduceIte, Hif]]
      iapply HΦ; itrivial
    · have hs : showsL x y x.Key' r = decide (y.Err' = W64 2 ∨ y.Err' = W64 3 ∨ y.Err' = W64 5) := by
        simp only [showsL, if_neg hk5, if_neg hk4, ne_eq, not_true_eq_false, ↓reduceIte, if_neg Hif]
      rw [hs]
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        rw [show decide (y.Err' = W64 2 ∨ y.Err' = W64 3 ∨ y.Err' = W64 5) = true by simp_all]
        iapply HΦ; itrivial
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          rw [show decide (y.Err' = W64 2 ∨ y.Err' = W64 3 ∨ y.Err' = W64 5) = true by simp_all]
          iapply HΦ; itrivial
        · (try wp_auto)
          wp_if_destruct
          · (try wp_auto)
            rw [show decide (y.Err' = W64 2 ∨ y.Err' = W64 3 ∨ y.Err' = W64 5) = true by simp_all]
            iapply HΦ; itrivial
          · (try wp_auto)
            rw [show decide (y.Err' = W64 2 ∨ y.Err' = W64 3 ∨ y.Err' = W64 5) = false by simp_all]
            iapply HΦ; itrivial
  · rw [show showsL x y key r = false by
      simp only [showsL, if_neg hk5, if_neg hk4, ne_eq, Hif, not_false_eq_true, ↓reduceIte]]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
