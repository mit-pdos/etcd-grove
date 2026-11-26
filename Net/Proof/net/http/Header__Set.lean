/-
The proof of `http.Header.Set` (`Net/Spec/net/http/Header__Set.lean`): `textproto.MIMEHeader(h).Set(key,
value)` (`MIMEHeader.Set.spec`): the map of `hdrOwn h hb` with `key` set to a fresh `[value]` is the map of
`hdrSetL hb key value` (the other lines' slices unchanged; `key`'s old ones dropped).
-/
module

public import Net.Spec.net.http.Header__Set
public import Net.Spec.net.textproto.MIMEHeader__Set

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section pure

/-- A name other than `key` is one of `hdrSetL hb key v`'s names iff it is one of `hb`'s. -/
theorem mem_fst_hdrSetL (hb : List HdrLine) (k key v : GoString) (hk : k ≠ key) :
    k ∈ (hdrSetL hb key v).map Prod.fst ↔ k ∈ hb.map Prod.fst := by
  unfold hdrSetL
  simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton, hk,
    _root_.or_false, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, -⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ⟨ha, by simpa using hk⟩, rfl⟩

end pure

section lemma
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The lines not named `key` keep their slices in the map with `key` set. -/
theorem hdrEls_set (ms : GMap GoString GoSlice) (key : GoString) (s' : GoSlice) (l : List HdrLine) :
    ([∗list] kv ∈ l, ∃ s : GoSlice, ⌜ms !! kv.1 = some s⌝ ∗ s ↦* ([kv.2] : List GoString) : IProp GF) ⊢
    [∗list] kv ∈ l.filter (fun kv => decide (kv.1 ≠ key)),
      ∃ s : GoSlice, ⌜(<[key := s']> ms) !! kv.1 = some s⌝ ∗ s ↦* ([kv.2] : List GoString) := by
  induction l with
  | nil =>
    rw [List.filter_nil]
    iintro -
    iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
    itrivial
  | cons a l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    by_cases ha : a.1 = key
    · rw [List.filter_cons_of_neg (by simp [ha])]
      iapply ih $$ H
    · rw [List.filter_cons_of_pos (by simp [ha])]
      iapply BigSepL.bigSepL_cons.2
      isplitl [Ha]
      · icases Ha with ⟨%s, %hs, Hs⟩
        iexists s
        iframe Hs
        ipureintro
        rw [GMap.lookup_insert_ne _ _ (Ne.symm ha)]; exact hs
      · iapply ih $$ H

end lemma

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Header.Set.wp_proof
    (wp_Set : net.textproto.MIMEHeader.Set.spec (GF := GF) (hG := hG)) :
    Header.Set.spec (GF := GF) (hG := hG) := by
  intro h hb key value Hk
  wp_start as Hown
  iunfold hdrOwn at Hown
  icases Hown with ⟨%ms, Hm, %Hdom, Hels⟩
  wp_auto
  wp_apply wp_Set h ms key value $$ [Hm] as %s ⟨Hm, Hs⟩
  · iframe; ipureintro; exact Hk
  iapply HΦ
  iunfold hdrOwn
  iexists (<[key := s]> ms)
  iframe Hm
  isplitr
  · ipureintro
    intro k
    by_cases hk : k = key
    · subst hk; simp [hdrSetL]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), Hdom k]
      simp only [mem_fst_hdrSetL hb k key value hk]
  unfold hdrSetL
  iapply BigSepL.bigSepL_snoc.2
  isplitl [Hels]
  · iapply hdrEls_set ms key s hb $$ Hels
  · iexists s
    iframe Hs
    ipureintro
    exact GMap.lookup_insert _ _ _

end proof

end net.http
end Perennial
