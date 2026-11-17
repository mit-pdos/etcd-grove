module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bookmarksOk

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem bookmarksOk.wp_proof : bookmarksOk.spec (GF := GF) (hG := hG) := by
  intro s evs
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  ihave HI : (∃ (i : w64) (evv : WEvent) (lb le : w64) (ann : Bool),
      "i" ∷ i_ptr ↦ i ∗ "ev" ∷ ev_ptr ↦ evv ∗
      "lastBookmark" ∷ lastBookmark_ptr ↦ lb ∗ "lastEvent" ∷ lastEvent_ptr ↦ le ∗
      "annotated" ∷ annotated_ptr ↦ ann ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len ∧
        ((ws.map wevOf).take (sint.nat i)).foldl bmStepL (some (0, 0, false)) =
          some (uint.nat lb, uint.nat le, ann)⌝ : IProp GF)
      $$ [i ev lastBookmark lastEvent annotated]
  · iexists W64 0, _, W64 0, W64 0, false
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨Hi.1, Hif⟩
    list_elem ws (sint.nat i) as w
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z i) ws _ w Hi.1 $$ [Hk] as -
    · isplit
      · iexact Hk
      · ipureintro; exact Hw_lookup
    have hl : (ws.map wevOf)[sint.nat i]? = some (wevOf w) := by simp [Hw_lookup]
    have hstep : ((ws.map wevOf).take (sint.nat i + 1)).foldl bmStepL (some (0, 0, false)) =
        bmStepL (some (uint.nat lb, uint.nat le, ann)) (wevOf w) := by
      rw [List.take_add_one, hl, Option.toList_some, List.foldl_append, Hi.2.2]; rfl
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have hfalse : bmStepL (some (uint.nat lb, uint.nat le, ann)) (wevOf w) = none →
        bookmarksOkL (ws.map wevOf) = false := fun hn => bookmarksOkL_false_of _ _ _ _ hl Hi.2.2 hn
    wp_if_destruct
    · have hT := Hif; clear Hif
      wp_if_destruct
      · wp_for_post
        rw [hfalse (by rw [bmStepL_wev]; simp only [hT, Hif, _root_.true_or, ↓reduceIte])]
        iapply HΦ; itrivial
      · have h1 := Hif; clear Hif
        wp_if_destruct
        · wp_for_post
          rw [hfalse (by rw [bmStepL_wev]; simp only [hT, Hif, _root_.or_true, ↓reduceIte])]
          iapply HΦ; itrivial
        · have h2 := Hif; clear Hif
          have hc : ¬ (uint.Z w.Obj'.ResourceVersion' < uint.Z lb ∨
              uint.Z w.Obj'.ResourceVersion' < uint.Z le) := by omega
          cases hA : w.Obj'.Annotated'
          · wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, w, w.Obj'.ResourceVersion', le, ann
            iframe
            ipureintro; refine ⟨by word, by word, ?_⟩
            rw [hi1, hstep, bmStepL_wev]
            simp only [hT, hc, hA, ↓reduceIte, Bool.false_eq_true]
          · wp_auto
            wp_if_destruct
            · wp_for_post
              iframe
              iexists i + W64 1, w, w.Obj'.ResourceVersion', le, true
              iframe
              ipureintro; refine ⟨by word, by word, ?_⟩
              rw [hi1, hstep, bmStepL_wev]
              simp only [hT, hc, hA, ↓reduceIte, Bool.false_eq_true]
            · wp_for_post
              rw [hfalse (by rw [bmStepL_wev]; simp only [hT, hc, hA, ↓reduceIte])]
              iapply HΦ; itrivial
    · have hT := Hif; clear Hif
      wp_if_destruct
      · wp_for_post
        rw [hfalse (by rw [bmStepL_wev]; simp only [hT, Hif, ↓reduceIte])]
        iapply HΦ; itrivial
      · have h1 := Hif; clear Hif
        wp_if_destruct
        · wp_for_post
          iframe
          iexists i + W64 1, w, lb, w.Obj'.ResourceVersion', ann
          iframe
          ipureintro; refine ⟨by word, by word, ?_⟩
          rw [hi1, hstep, bmStepL_wev]
          simp only [hT, h1, Hif, ↓reduceIte]
        · wp_for_post
          iframe
          iexists i + W64 1, w, lb, le, ann
          iframe
          ipureintro; refine ⟨by word, by word, ?_⟩
          rw [hi1, hstep, bmStepL_wev]
          simp only [hT, h1, Hif, ↓reduceIte]
  · have htake : (ws.map wevOf).take (sint.nat i) = ws.map wevOf :=
      List.take_of_length_le (by simp; word)
    have : bookmarksOkL (ws.map wevOf) = true := by
      unfold bookmarksOkL; rw [← htake, Hi.2.2]; rfl
    rw [this]
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
