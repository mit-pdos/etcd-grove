/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.splitInitialEvents` on the accepting run: the loop visits events that
are not bookmarks until the first bookmark (`splitInitL`'s index), whose annotation is set
(`annotObj`), and returns the slices around it (`evsRO_split`); with no bookmark, the filtered events
are empty and the result is `nil, nil, nil`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__splitInitialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.filterOutBookmarksAndErrors
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

theorem findIdx_bm {rs : List REv} {j : Nat} {r : REv} (hr : rs[j]? = some r) (hb : r.ty = evBookmark)
    (hpre : ∀ r ∈ rs.take j, r.ty ≠ evBookmark) :
    rs.findIdx? (fun e => decide (e.ty = evBookmark)) = some j := by
  induction rs generalizing j with
  | nil => simp at hr
  | cons x xs ih =>
    cases j with
    | zero =>
      simp at hr; subst hr
      simp [List.findIdx?_cons, hb]
    | succ j =>
      have hx : x.ty ≠ evBookmark := hpre x (by simp)
      have := ih (j := j) (by simpa using hr) (fun r hr' => hpre r (by simp [hr']))
      simp [List.findIdx?_cons, hx, this]

theorem splitInitL_bm {rs a b : List REv} {j : Nat} {r : REv} (hok : splitInitL rs = some (a, b))
    (hr : rs[j]? = some r) (hb : r.ty = evBookmark) (hpre : ∀ r ∈ rs.take j, r.ty ≠ evBookmark) :
    ∃ o, r.o = .obj o ∧ o.Annotated' = true ∧ a = rs.take j ∧ b = rs.drop j := by
  unfold splitInitL at hok
  rw [findIdx_bm hr hb hpre] at hok
  simp only [List.getD_eq_getElem?_getD, hr, Option.getD_some] at hok
  revert hok
  cases ho : r.o with
  | obj o =>
    simp only [annotL]
    cases ha : o.Annotated' with
    | false => intro h; cases h
    | true => intro h; cases h; exact ⟨o, rfl, ha, rfl, rfl⟩
  | status s => simp [annotL]
  | other => simp [annotL]

theorem splitInitL_nobm {rs a b : List REv} (hok : splitInitL rs = some (a, b))
    (hpre : ∀ r ∈ rs, r.ty ≠ evBookmark) :
    (filterBE rs).length = 0 ∧ a = [] ∧ b = [] := by
  unfold splitInitL at hok
  have hn : rs.findIdx? (fun e => decide (e.ty = evBookmark)) = none := by
    rw [List.findIdx?_eq_none_iff]; intro x hx; simpa using hpre x hx
  rw [hn] at hok
  simp only at hok
  split at hok
  · rename_i he
    cases hok
    exact ⟨by simpa using he, rfl, rfl⟩
  · cases hok

theorem WatchValidator.splitInitialEvents.wp_proof
    (wp_filter : filterOutBookmarksAndErrors.spec (GF := GF) (hG := hG))
    [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
    [meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]
    [runtime_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]
    (wp_HI : storage.HasInitialEventsEndBookmarkAnnotation.spec (GF := GF) (hG := hG))
    (wp_GA : k8s_etcd3.Obj.GetAnnotations.spec (GF := GF) (hG := hG)) :
    WatchValidator.splitInitialEvents.spec (GF := GF) (hG := hG) := by
  have wp_annot := annotObj.wp_ok wp_HI wp_GA
  intro rp sl rs a b hok
  wp_start as #Hs
  ihave #Hs0 := Hs
  iunfold evsRO at Hs0
  icases Hs0 with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hwf := ownSlice_wf $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  wp_auto
  rename_i iv_ptr
  irename : (iv_ptr ↦ (zero_val w64) : IProp GF) => i0
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ ev ∗ "i0" ∷ iv_ptr ↦ iv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        ∀ r ∈ rs.take (sint.nat j), r.ty ≠ evBookmark⌝ : IProp GF) $$ [i ev i0]
  · iexists W64 0, _, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z sl.len := by simpa using Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif'⟩
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
    iunfold evRep at Hv
    icases Hv with ⟨%hty, #Ho⟩
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    by_cases hb : r.ty = evBookmark
    · obtain ⟨o, ho, hann, ha, hb'⟩ := splitInitL_bm hok hr hb Hj.2.2
      subst ha hb'
      have hev : v.Type' = go!"BOOKMARK" := by rw [hty, hb]; rfl
      simp only [hev, decide_true, Bool.not_true]
      wp_auto
      isimp only [ho] at Ho
      iunfold evObjRep at Ho
      wp_apply (wp_annot v.Object' o) $$ [Ho]
      · iframe #
      rw [hann]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hj.1, by word⟩)]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, by word, by word⟩)]
      wp_auto
      icases evsRO_split sl rs j ⟨Hj.1, by word⟩ $$ Hs with ⟨#H1, #H2⟩
      wp_for_post
      iapply HΦ
      iframe H1 H2
      ipureintro; rfl
    · have hev : v.Type' ≠ go!"BOOKMARK" := by rw [hty]; exact hb
      simp only [decide_eq_false hev]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, v, j
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hj1, List.take_add_one, hr]
      intro r' hr'
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hr'
      rcases hr' with hr' | rfl
      · exact Hj.2.2 r' hr'
      · exact hb
  · have hjl : sint.nat j = rs.length := by rw [← Hl2]; word
    have hpre : ∀ r ∈ rs, r.ty ≠ evBookmark := by
      have := Hj.2.2; rwa [hjl, List.take_length] at this
    obtain ⟨hf0, ha, hb⟩ := splitInitL_nobm hok hpre
    subst ha hb
    (try wp_auto)
    wp_apply (wp_filter sl rs) $$ [] as %fsl #Hf
    · iframe #
    iunfold evsRO at Hf
    icases Hf with ⟨%fvs, #Hfsl, #Hfvs⟩
    ihave %Hfl := ownSlice_len $$ Hfsl
    ihave %Hfl2 := BigSepL2.bigSepL2_length $$ Hfvs
    have hfz : fsl.len = W64 0 := by
      have : sint.nat fsl.len = 0 := by rw [← Hfl.1, Hfl2, hf0]
      word
    rw [hfz]
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    isplitl [] <;> iapply evsRO_nil

end proof

end k8s_correctness
end EtcdGrove
end Perennial
