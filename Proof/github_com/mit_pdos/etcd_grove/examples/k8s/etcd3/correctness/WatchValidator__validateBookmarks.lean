/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.validateBookmarks` on the accepting run: the loop's state is
`bookmarksOkR`'s fold over the events visited (`bmStepR`), which stays `some` on an accepted list
(`bmFold_take_some`); each step's facts (`bmStepR_some`) rule out the rejecting branches: an event
other than an Error holds a driver's `*Obj` (`objectRV`, the annotation through `annotObj`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__validateBookmarks
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.objectRV
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem bmFold_none (l : List REv) : l.foldl bmStepR none = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa [List.foldl, bmStepR] using ih

/-- On an accepted list, every prefix's fold is `some`. -/
theorem bmFold_take_some {rs : List REv} (h : bookmarksOkR rs = true) (j : Nat) :
    ∃ acc, (rs.take j).foldl bmStepR (some (0, 0, false)) = some acc := by
  unfold bookmarksOkR at h
  rw [← List.take_append_drop j rs, List.foldl_append] at h
  cases hf : (rs.take j).foldl bmStepR (some (0, 0, false)) with
  | none => rw [hf, bmFold_none] at h; cases h
  | some acc => exact ⟨acc, rfl⟩

/-- What a step of `bmStepR` that does not fail says. -/
theorem bmStepR_some {lb le : w64} {f : Bool} {r : REv} {acc : w64 × w64 × Bool}
    (h : bmStepR (some (lb, le, f)) r = some acc) :
    (r.ty = evError → acc = (lb, le, f)) ∧
    (r.ty ≠ evError → ∃ o, r.o = .obj o ∧
      (r.ty = evBookmark → uint.nat lb ≤ uint.nat o.ResourceVersion' ∧
        uint.nat le ≤ uint.nat o.ResourceVersion' ∧ (o.Annotated' = true → f = false) ∧
        acc = (o.ResourceVersion', le, f || o.Annotated')) ∧
      (r.ty ≠ evBookmark → uint.nat lb < uint.nat o.ResourceVersion' ∧
        acc = (lb, wmax le o.ResourceVersion', f))) := by
  unfold bmStepR at h
  by_cases he : r.ty = evError
  · simp only [he, ↓reduceIte, Option.some.injEq] at h
    exact ⟨fun _ => h.symm, fun h' => absurd he h'⟩
  refine ⟨fun h' => absurd h' he, fun _ => ?_⟩
  simp only [he, ↓reduceIte] at h
  cases ho : r.o with
  | status s => rw [ho] at h; cases h
  | other => rw [ho] at h; cases h
  | obj o =>
    rw [ho] at h
    simp only [objRVL, annotL] at h
    refine ⟨o, rfl, fun hb => ?_, fun hb => ?_⟩
    · simp only [hb, ↓reduceIte] at h
      by_cases h1 : uint.nat o.ResourceVersion' < uint.nat lb ∨
          uint.nat o.ResourceVersion' < uint.nat le
      · simp only [h1, ↓reduceIte] at h; cases h
      simp only [h1, ↓reduceIte] at h
      simp only [not_or, Nat.not_lt] at h1
      refine ⟨h1.1, h1.2, ?_⟩
      cases ha : o.Annotated' <;> cases hf : f <;> simp [ha, hf] at h ⊢ <;> exact h.symm
    · simp only [hb, ↓reduceIte] at h
      by_cases h1 : uint.nat o.ResourceVersion' ≤ uint.nat lb
      · simp only [h1, ↓reduceIte] at h; cases h
      simp only [h1, ↓reduceIte, Option.some.injEq] at h
      simp only [Nat.not_le] at h1
      exact ⟨h1, h.symm⟩

theorem WatchValidator.validateBookmarks.wp_proof
    (wp_objectRV : objectRV.spec (GF := GF) (hG := hG))
    [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
    [meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]
    [runtime_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]
    (wp_HI : storage.HasInitialEventsEndBookmarkAnnotation.spec (GF := GF) (hG := hG))
    (wp_GA : k8s_etcd3.Obj.GetAnnotations.spec (GF := GF) (hG := hG)) :
    WatchValidator.validateBookmarks.spec (GF := GF) (hG := hG) := by
  have wp_annot := annotObj.wp_ok wp_HI wp_GA
  intro rp sl rs hok
  wp_start as #Hs
  iunfold evsRO at Hs
  icases Hs with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  wp_auto
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (lb le : w64) (f : Bool),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ ev ∗ "lastBookmarkRV" ∷ lastBookmarkRV_ptr ↦ lb ∗
      "lastEventRV" ∷ lastEventRV_ptr ↦ le ∗ "initialEventBookmarkFound" ∷ initialEventBookmarkFound_ptr ↦ f ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        (rs.take (sint.nat j)).foldl bmStepR (some (0, 0, false)) = some (lb, le, f)⌝ : IProp GF)
      $$ [i ev lastBookmarkRV lastEventRV initialEventBookmarkFound]
  · iexists W64 0, _, W64 0, W64 0, false
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HL
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem vs (sint.nat j) as v
    wp_apply (wp_load_slice_index sl (sint.Z j) vs DFrac.discard v Hj.1) $$ [Hsl] as -
    · isplit
      · iexact Hsl
      · ipureintro; exact Hv_lookup
    obtain ⟨r, hr⟩ : ∃ r, rs[sint.nat j]? = some r := by
      have : sint.nat j < rs.length := by rw [← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave #Hv := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      Hv_lookup hr $$ Hvs
    ihave #Hv' := Hv
    iunfold evRep at Hv'
    icases Hv' with ⟨%hty, #Ho⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : rs.take (sint.nat j + 1) = rs.take (sint.nat j) ++ [r] := by
      rw [List.take_add_one, hr]; rfl
    obtain ⟨acc, hacc⟩ := bmFold_take_some hok (sint.nat j + 1)
    rw [htake, List.foldl_append, Hj.2.2] at hacc
    simp only [List.foldl_cons, List.foldl_nil] at hacc
    obtain ⟨hE, hN⟩ := bmStepR_some hacc
    (try wp_auto)
    by_cases he : r.ty = evError
    · have hev : v.Type' = go!"ERROR" := by rw [hty, he]; rfl
      simp only [hev, decide_true]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, v, lb, le, f
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hj1, htake, List.foldl_append, Hj.2.2]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hacc, hE he]
    · have hev : v.Type' ≠ go!"ERROR" := by rw [hty]; exact he
      simp only [decide_eq_false hev]
      (try wp_auto)
      obtain ⟨o, hro, hB, hNB⟩ := hN he
      isimp only [hro] at Ho
      iunfold evObjRep at Ho
      wp_apply (wp_objectRV v.Object' o) $$ [Ho]
      · iframe #
      have hfold : ∀ acc', acc' = acc →
          (rs.take (sint.nat (j + W64 1))).foldl bmStepR (some (0, 0, false)) = some acc' := by
        intro acc' h'
        rw [h', hj1, htake, List.foldl_append, Hj.2.2]
        simpa using hacc
      by_cases hb : r.ty = evBookmark
      · obtain ⟨h1, h2, h3, hacc'⟩ := hB hb
        have hevB : v.Type' = go!"BOOKMARK" := by rw [hty, hb]; rfl
        simp only [hevB, decide_true]
        (try wp_auto)
        wp_if_destruct
        · exfalso; word
        (try wp_auto)
        wp_if_destruct
        · exfalso; word
        (try wp_auto)
        wp_apply (wp_annot v.Object' o) $$ [Ho]
        · iframe #
        (try wp_auto)
        cases ha : o.Annotated'
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, v, o.ResourceVersion', le, f
          iframe
          ipureintro
          refine ⟨by word, by word, hfold _ ?_⟩
          rw [hacc', ha, Bool.or_false]
        · have hf : f = false := h3 ha
          subst hf
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, v, o.ResourceVersion', le, true
          iframe
          ipureintro
          refine ⟨by word, by word, hfold _ ?_⟩
          rw [hacc', ha]
      · obtain ⟨h1, hacc'⟩ := hNB hb
        have hevB : v.Type' ≠ go!"BOOKMARK" := by rw [hty]; exact hb
        simp only [decide_eq_false hevB]
        (try wp_auto)
        wp_if_destruct
        · exfalso; word
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, v, lb, o.ResourceVersion', f
          iframe
          ipureintro
          refine ⟨by word, by word, hfold _ ?_⟩
          rw [hacc']
          have : wmax le o.ResourceVersion' = o.ResourceVersion' := by
            unfold wmax; split <;> word
          rw [this]
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, v, lb, le, f
          iframe
          ipureintro
          refine ⟨by word, by word, hfold _ ?_⟩
          rw [hacc']
          have : wmax le o.ResourceVersion' = le := by
            unfold wmax; split
            · rename_i hle; word
            · rfl
          rw [this]
  · (try wp_auto)
    iapply HΦ; ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
