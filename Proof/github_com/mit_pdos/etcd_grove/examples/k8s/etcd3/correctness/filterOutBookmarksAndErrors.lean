/-
Lean-first (no Rocq counterpart).

The proof of `filterOutBookmarksAndErrors`: the loop keeps the filtered prefix (`filterBE` of the
events visited), each kept event's view carried over.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.filterOutBookmarksAndErrors

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

theorem filterOutBookmarksAndErrors.wp_proof :
    filterOutBookmarksAndErrors.spec (GF := GF) (hG := hG) := by
  intro sl rs
  wp_start as #Hs
  unfold evsRO
  icases Hs with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  wp_auto
  wp_apply (wp_slice_make3 (V := k8s_io.apimachinery.pkg.watch.Event) (W64 0) sl.len (by word))
    as %fsl ⟨Hf, Hfc, -⟩
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (esl : GoSlice)
      (gs : List k8s_io.apimachinery.pkg.watch.Event),
      "i" ∷ i_ptr ↦ j ∗ "event" ∷ event_ptr ↦ ev ∗ "filtered" ∷ filtered_ptr ↦ esl ∗
      "He" ∷ esl ↦* gs ∗ "Hc" ∷ ownSliceCap k8s_io.apimachinery.pkg.watch.Event esl (DFrac.own 1) ∗
      "#Hg" ∷ ([∗list] g;r ∈ gs;filterBE (rs.take (sint.nat j)), evRep g r) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i event filtered Hf Hfc]
  · iexists W64 0, _, fsl, []
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl
    · simp only [named, filterBE, List.filter_nil]
      iapply BigSepL2.bigSepL2_nil.2
      itrivial
    ipureintro; refine ⟨by word, by word⟩
  iapply wp_fupd
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
    have hfs : filterBE (rs.take (sint.nat j + 1)) = filterBE (rs.take (sint.nat j)) ++
        (if decide (r.ty = evBookmark) || decide (r.ty = evError) then [] else [r]) := by
      rw [htake]; unfold filterBE; rw [List.filter_append]
      by_cases h1 : r.ty = evBookmark <;> by_cases h2 : r.ty = evError <;> simp [h1, h2]
    (try wp_auto)
    by_cases hbe : (decide (r.ty = evBookmark) || decide (r.ty = evError)) = true
    · simp only [hbe, ↓reduceIte, List.append_nil] at hfs
      have hbe' : r.ty = evBookmark ∨ r.ty = evError := by simpa using hbe
      have hev : v.Type' = evBookmark ∨ v.Type' = evError := by rw [hty]; exact hbe'
      rcases hev with hb | he
      · simp (config := { decide := true }) only [hb, evBookmark]
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, v, esl, gs
        rw [hj1, hfs]
        iframe
        isplitl []
        · iexact Hg
        ipureintro; refine ⟨by word, by word⟩
      · simp (config := { decide := true }) only [he, evError]
        wp_auto
        simp (config := { decide := true }) only [he, evError]
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, v, esl, gs
        rw [hj1, hfs]
        iframe
        isplitl []
        · iexact Hg
        ipureintro; refine ⟨by word, by word⟩
    · simp only [hbe, Bool.false_eq_true, ↓reduceIte] at hfs
      have hb : v.Type' ≠ evBookmark := by rw [hty]; intro h; apply hbe; simp [h]
      have he : v.Type' ≠ evError := by rw [hty]; intro h; apply hbe; simp [h]
      unfold evBookmark at hb
      unfold evError at he
      simp only [decide_eq_false hb]
      wp_auto
      simp only [decide_eq_false he]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %nsl ⟨Hn, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$He $Hc $Hn] as %esl' ⟨He, Hc, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, v, esl', _
      rw [hj1, hfs]
      iframe
      isplitl []
      · simp only [named]
        iapply (BigSepL2.bigSepL2_snoc).2
        iframe Hg
        iexact Hv
      ipureintro; refine ⟨by word, by word⟩
  · have hjl : sint.nat j = rs.length := by rw [← Hl2]; word
    isimp only [hjl, List.take_length] at Hg
    (try wp_auto)
    ipersist He
    imodintro
    iapply HΦ
    iexists gs
    isplitl []
    · iexact He
    · iexact Hg

end proof

end k8s_correctness
end EtcdGrove
end Perennial
