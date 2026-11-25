/-
net/http's `parsePattern` on a literal path pattern (`litPat`, `MuxTree.lean`): no method, no host,
its segments `pathSegs p` (`segVal`), no error.
-/
module

public import Net.Proof.net.http.MuxTree
public import Perennial.Spec.strings.IndexAny

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

theorem getElem?_ne_of_pathByte (s : List w8) (hs : ∀ b ∈ s, pathByte b = true) (c : w8)
    (hc : pathByte c = false) (j : Nat) : s[j]? ≠ some c := by
  intro hj
  have := hs c (List.mem_of_getElem? hj)
  rw [hc] at this; exact Bool.false_ne_true this

theorem indexAnyByte_none (s chars : List w8) (h : ∀ b ∈ s, b ∉ chars) :
    strings.indexAnyByte s chars = -1 := by
  unfold strings.indexAnyByte
  have : s.findIdx (fun b => decide (b ∈ chars)) = s.length := by
    rw [List.findIdx_eq_length]; intro b hb; simpa using h b hb
  rw [this]; simp

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

set_option maxRecDepth 20000 in
/-- `parsePattern(p)` of a literal pattern. -/
theorem wp_parsePattern_lit (wp_IndexAny : strings.IndexAny.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (p : List w8) (hp : litPat p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
      (App (Val (@! net.http.parsePattern)) (Val #p))
    {{ (pp : Loc) (sl : GoSlice), RET (PairV #pp #(interface.nil : GoInterface));
        pp ↦ ({ str' := p, method' := [], host' := [], segments' := sl, loc' := [] } : net.http.pattern) ∗
        sl ↦* ((pathSegs p).map segVal) ∗ ownSliceCap net.http.segment sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hstr, #Hurl⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  have hpne : p ≠ [] := by intro h; rw [h] at hp; simp [litPat] at hp
  wp_apply wp_string_len as %Hl
  try wp_auto
  rw [decide_eq_false (show W64 (p.length : Int) ≠ W64 0 by
    have : 0 < p.length := List.length_pos_iff.mpr hpne; word)]
  try wp_auto
  wp_apply wp_IndexAny p _ as %i %Hi
  have hi : i = W64 (-1) := by
    rw [Hi (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> decide)]
    rw [indexAnyByte_none]
    intro b hb hbc
    have := hp.2 b hb
    simp at hbc; rcases hbc with rfl | rfl <;> simp [pathByte] at this
  subst hi
  try wp_auto
  have hp0 : p[0]? = some (W8 47) := by
    cases p with | nil => exact absurd rfl hpne | cons a l => simpa [litPat] using hp.1
  wp_apply wp_IndexByte
  rw [internal.bytealg.indexByte_eq_of p (W8 47) 0 hp0 (fun j hj => absurd hj (Nat.not_lt_zero _))]
  try wp_auto
  have eh : List.take (sint.nat (W64 ((0:Nat):Int)) - 0) (List.drop 0 p) = [] := by simp
  rw [eh]
  wp_apply wp_string_len as %_
  try wp_auto
  rw [ite_eq_left (by word)]
  have er : List.take (sint.nat (W64 ↑p.length) - sint.nat (W64 ((0:Nat):Int)))
      (List.drop (sint.nat (W64 ((0:Nat):Int))) p) = p := by
    rw [show sint.nat (W64 ((0:Nat):Int)) = 0 by word, List.drop_zero]
    apply List.take_of_length_le; word
  rw [er]
  try wp_auto
  wp_apply wp_IndexByte
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %m' HM
  try wp_auto
  ihave Hsl0 := ownSlice_nil (V := net.http.segment) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := net.http.segment) (GF := GF)
  ihave HI : (∃ (r : List w8) (sl : GoSlice) (acc : List Seg) (o : w64),
      "rest" ∷ rest_ptr ↦ r ∗ "off" ∷ off_ptr ↦ o ∗
      "P" ∷ «$r0_ptr» ↦ ({ str' := p, method' := [], host' := [], segments' := sl, loc' := [] } : net.http.pattern) ∗
      "Hsl" ∷ sl ↦* acc.map segVal ∗ "Hcap" ∷ ownSliceCap net.http.segment sl (DFrac.own 1) ∗
      "%Hr" ∷ ⌜acc ++ pathSegs r = pathSegs p ∧ (r = [] ∨ r.head? = some (W8 47)) ∧
        (∀ b ∈ r, pathByte b = true) ∧ r.length ≤ p.length⌝ : IProp GF) $$ [rest off «$r0» Hsl0 Hcap0]
  · iexists p, slice.nil, [], _
    simp only [List.map_nil, List.nil_append]
    iframe
    isplitl [Hsl0]
    · iexact Hsl0
    isplitl [Hcap0]
    · iexact Hcap0
    ipureintro; exact ⟨trivial, .inr hp.1, hp.2, Nat.le_refl _⟩
  wp_for HI
  obtain rfl | ⟨t, rfl⟩ : r = [] ∨ ∃ t, r = W8 47 :: t := by
    rcases Hr.2.1 with h | h
    · exact .inl h
    · cases r with
      | nil => exact .inl rfl
      | cons c t => simp at h; subst h; exact .inr ⟨t, rfl⟩
  · wp_apply wp_string_len as %Hrl
    try wp_auto
    simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    simp only [decide_true, ↓reduceIte]
    try wp_auto
    have hacc : acc = pathSegs p := by have := Hr.1; simpa [pathSegs] using this
    subst hacc
    iapply HΦ
    iframe
  · wp_apply wp_string_len as %Hrl
    try wp_auto
    have hlt : t.length + 1 < 2 ^ 63 := by have := Hr.2.2.2; simp only [List.length_cons] at this; omega
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 ↑(W8 47 :: t).length) by
      simp only [List.length_cons]; word)]
    simp only [decide_true, ↓reduceIte]
    try wp_auto
    wp_apply wp_string_len as %_
    try wp_auto
    rw [ite_eq_left (by simp only [List.length_cons]; word)]
    have e1 : List.take (sint.nat (W64 ↑(W8 47 :: t).length) - 1)
        (List.drop 1 (W8 47 :: t)) = t := by
      simp only [List.drop_succ_cons, List.drop_zero]; apply List.take_of_length_le
      simp only [List.length_cons]; word
    rw [e1]
    try wp_auto
    wp_apply wp_string_len as %_
    try wp_auto
    wp_apply wp_string_len as %_
    try wp_auto
    wp_apply wp_string_len as %_
    try wp_auto
    by_cases ht : t = []
    · subst ht
      rw [decide_eq_true (show W64 ↑([] : List w8).length = W64 0 by simp)]
      try wp_auto
      wp_apply wp_slice_literal (V := net.http.segment) [segVal .multi]
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := net.http.segment) _ _ _ _ _ $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
      try wp_auto
      wp_for_post
      try wp_auto
      have hacc : List.map segVal acc ++ [segVal Seg.multi] = List.map segVal (pathSegs p) := by
        rw [← Hr.1, pathSegs_slash]; simp
      rw [hacc]
      iapply HΦ
      iframe
    · rw [decide_eq_false (show W64 ↑t.length ≠ W64 0 by
        have : 0 < t.length := List.length_pos_iff.mpr ht; word)]
      try wp_auto
      wp_apply wp_IndexByte
      have htb : ∀ b ∈ t, pathByte b = true := fun b hb => Hr.2.2.1 b (by simp [hb])
      rcases slash_split t with ⟨hi, htw, hdw⟩ | ⟨i, hi, hidx, htw, hdw⟩
      · rw [hi]
        try wp_auto
        wp_apply wp_string_len as %_
        try wp_auto
        rw [ite_eq_left (by word)]
        have e1 : List.take (sint.nat (W64 ↑t.length) - 0) (List.drop 0 t) = t := by
          simp only [List.drop_zero]; apply List.take_of_length_le; word
        rw [e1]
        try wp_auto
        wp_apply wp_string_len as %_
        try wp_auto
        rw [ite_eq_left (by word)]
        have e2 : List.take (sint.nat (W64 ↑t.length) - sint.nat (W64 ↑t.length))
            (List.drop (sint.nat (W64 ↑t.length)) t) = [] := by simp
        rw [e2]
        try wp_auto
        wp_apply wp_IndexByte
        rw [internal.bytealg.indexByte_eq_neg t (W8 123)
          (getElem?_ne_of_pathByte t htb (W8 123) (by decide))]
        try wp_auto
        wp_apply wp_pathUnescape wp_PathUnescape t
          (fun b hb => pathByte_ne_pct b (htb b hb)) $$ [$Hpkg2]
        try wp_auto
        wp_apply wp_slice_literal (V := net.http.segment) [segVal (.lit t)]
        isplitr
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_apply wp_slice_append (V := net.http.segment) _ _ _ _ _ $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
        try wp_auto
        wp_for_post
        iframe
        iexists [], sl', acc ++ [.lit t], _
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        ipureintro
        refine ⟨?_, by simp, by simp, by simp⟩
        rw [← Hr.1, pathSegs_cons t ht, htw, hdw]; simp
      · rw [hidx]
        try wp_auto
        rw [decide_eq_false (show ¬ sint.Z (W64 ↑i) < sint.Z (W64 0) by word)]
        try wp_auto
        rw [ite_eq_left (by word)]
        have e1 : List.take (sint.nat (W64 ↑i) - 0) (List.drop 0 t) = t.take i := by
          simp only [List.drop_zero, Nat.sub_zero]; congr 1; word
        rw [e1]
        try wp_auto
        wp_apply wp_string_len as %_
        try wp_auto
        rw [ite_eq_left (by word)]
        have e2 : List.take (sint.nat (W64 ↑t.length) - sint.nat (W64 ↑i))
            (List.drop (sint.nat (W64 ↑i)) t) = t.drop i := by
          rw [show sint.nat (W64 ↑i) = i by word]
          apply List.take_of_length_le; simp only [List.length_drop]; word
        rw [e2]
        try wp_auto
        have htb' : ∀ b ∈ t.take i, pathByte b = true := fun b hb => htb b (List.mem_of_mem_take hb)
        wp_apply wp_IndexByte
        rw [internal.bytealg.indexByte_eq_neg (t.take i) (W8 123)
          (getElem?_ne_of_pathByte _ htb' (W8 123) (by decide))]
        try wp_auto
        wp_apply wp_pathUnescape wp_PathUnescape (t.take i)
          (fun b hb => pathByte_ne_pct b (htb' b hb)) $$ [$Hpkg2]
        try wp_auto
        wp_apply wp_slice_literal (V := net.http.segment) [segVal (.lit (t.take i))]
        isplitr
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_apply wp_slice_append (V := net.http.segment) _ _ _ _ _ $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
        try wp_auto
        wp_for_post
        iframe
        iexists t.drop i, sl', acc ++ [.lit (t.take i)], _
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        ipureintro
        have hne : t.drop i ≠ [] := by simp; omega
        refine ⟨?_, ?_, fun b hb => htb b (List.mem_of_mem_drop hb), ?_⟩
        · rw [← Hr.1, pathSegs_cons t ht, htw, hdw]; simp
        · right; have := dropWhile_shape t; rw [hdw] at this
          exact this.resolve_left hne
        · have := Hr.2.2.2; simp only [List.length_cons, List.length_drop] at this ⊢; omega

end wp

end net.http
end Perennial
