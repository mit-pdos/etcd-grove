/-
Proof of `LinuxFs/Spec/path/filepath/join.lean`: the range loop up to the first non-empty element,
then Perennial's `strings.Join` (`sep.intercalate`) of the rest and `Clean`; the model
(`path.joinModel`, the main tree's `path.Join` buffer) agrees (`filepath.joinModel_drop`). Lean-first.
-/
module

public import LinuxFs.Spec.path.filepath.join
public import LinuxFs.Spec.path.filepath.Clean
public import LinuxFs.Proof.internal.filepathlite.UntypedRune

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `Join`'s buffer from a non-empty buffer: each element after a slash. -/
theorem filepath.joinBuf_ne (rest : List (List w8)) (b : List w8) (hb : b ≠ []) :
    path.joinBuf rest b = b ++ (rest.map (fun x => path.slash :: x)).flatten := by
  induction rest generalizing b with
  | nil => simp [path.joinBuf]
  | cons x xs ih =>
    have hl : b.length > 0 := List.length_pos_iff.2 hb
    simp only [path.joinBuf, hl, true_or, ↓reduceIte]
    rw [ih _ (by simp [hb])]
    simp

/-- `intercalate [slash]` of a non-empty list. -/
theorem filepath.intercalate_cons (e : List w8) (rest : List (List w8)) :
    [path.slash].intercalate (e :: rest) = e ++ (rest.map (fun x => path.slash :: x)).flatten := by
  induction rest generalizing e with
  | nil => simp
  | cons x xs ih =>
    rw [List.intercalate_cons_cons, ih]
    simp

/-- Empty elements leave an empty buffer empty. -/
theorem filepath.joinBuf_empties (es : List (List w8)) (i : Nat) (hi : i ≤ es.length)
    (he : ∀ j < i, es[j]? = some []) (rest : List (List w8)) :
    path.joinBuf (es.take i ++ rest) [] = path.joinBuf rest [] := by
  induction i generalizing es with
  | zero => simp
  | succ i ih =>
    cases es with
    | nil => simp at hi
    | cons x xs =>
      have hx : x = [] := by simpa using he 0 (by omega)
      subst hx
      simp only [List.take_succ_cons, List.cons_append, path.joinBuf]
      simp only [List.length_nil, gt_iff_lt, Nat.lt_irrefl, ne_eq, not_true_eq_false, or_self,
        ↓reduceIte]
      exact ih xs (by simp at hi; omega) (fun j hj => by simpa using he (j + 1) (by omega))

/-- **The model from the first non-empty element `i`.** -/
theorem filepath.joinModel_drop (es : List (List w8)) (i : Nat) (hi : i < es.length)
    (he : ∀ j < i, es[j]? = some []) (hne : es[i] ≠ []) :
    path.joinModel es = path.cleanModel ([path.slash].intercalate (es.drop i)) := by
  have hsum : (es.map List.length).sum ≠ 0 := by
    intro h
    rw [List.sum_eq_zero_iff_forall_eq_nat] at h
    exact hne (List.length_eq_zero_iff.1 (h _ (List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩)))
  have hsplit : es = es.take i ++ (es[i] :: es.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hd : es.drop i = es[i] :: es.drop (i + 1) := List.drop_eq_getElem_cons hi
  rw [path.joinModel, if_neg hsum, hd]
  rw [congrArg (path.joinBuf · []) hsplit, filepath.joinBuf_empties es i (Nat.le_of_lt hi) he, filepath.intercalate_cons]
  simp only [path.joinBuf, List.length_nil, gt_iff_lt, Nat.lt_irrefl, ne_eq, hne,
    not_false_eq_true, or_true, ↓reduceIte, List.nil_append]
  rw [filepath.joinBuf_ne _ _ hne]

/-- **The model when every element is empty.** -/
theorem filepath.joinModel_empties (es : List (List w8)) (he : ∀ j < es.length, es[j]? = some []) :
    path.joinModel es = [] := by
  have hsum : (es.map List.length).sum = 0 := by
    rw [List.sum_eq_zero_iff_forall_eq_nat]
    intro n hn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := he j hj
    rw [List.getElem?_eq_getElem hj] at this
    simp [Option.some.inj this]
  simp [path.joinModel, hsum]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.path.filepath.Assumptions]

theorem filepath.join.wp_proof [UntypedRuneSemantics] (hClean : filepath.Clean.spec (GF := GF) (hG := hG)) :
    filepath.join.spec (GF := GF) (hG := hG) := by
  intro sl es dq
  wp_start as Hsl
  ihave %Hsll := ownSlice_len $$ Hsl
  try wp_auto
  rename_i ig_ptr
  ihave HI : (∃ (n : Nat) (ev : GoString) (gi : w64), "i" ∷ i_ptr ↦ W64 (n : Int) ∗
      "e" ∷ e_ptr ↦ ev ∗ "ig" ∷ ig_ptr ↦ gi ∗
      "%Hn" ∷ ⌜n ≤ es.length ∧ ∀ j < n, es[j]? = some []⌝ : IProp GF) $$ [-HΦ Hsl «$res0» elem]
  · iexists 0, _, _
    iframe
    ipureintro; exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  wp_for HI
  obtain ⟨Hnl, Hemp⟩ := Hn
  have Hn63 : n < 2 ^ 63 := by have := Hsll.1; word
  by_cases hn : n < es.length
  · have hc : sint.Z (W64 (n : Int)) < sint.Z sl.len := by
      have := Hsll.1; word
    rw [if_pos (decide_eq_true hc)]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hc⟩)]
    obtain ⟨ei, hei⟩ : ∃ e, es[n]? = some e := ⟨_, List.getElem?_eq_getElem hn⟩
    wp_apply wp_load_slice_index sl (sint.Z (W64 (n : Int))) es dq ei (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [show (sint.Z (W64 (n : Int))).toNat = n by word]; exact hei
    try wp_auto
    by_cases he : ei = []
    · subst he
      simp only [_root_.decide_true, Bool.not_true]
      try wp_auto
      wp_for_post
      iframe
      iexists n + 1, [], W64 (n : Int)
      rw [show W64 (((n + 1 : Nat) : Int)) = W64 (n : Int) + W64 1 by word]
      iframe
      ipureintro
      refine ⟨by omega, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact Hemp j h
      · subst h; exact hei
    · simp only [he, _root_.decide_false, Bool.not_false]
      try wp_auto
      ihave %Hwf := ownSlice_wf $$ Hsl
      have hlen : sint.Z sl.len = es.length := by have := Hsll.1; have := Hsll.2; word
      rw [if_pos ⟨by word, by word, Hwf.2⟩]
      try wp_auto
      icases (ownSlice_slice (V := GoString) (W64 (n : Int)) sl.len sl dq es
        ⟨by word, by word, Int.le_refl _⟩).1 $$ Hsl with ⟨H1, H2, H3⟩
      try wp_auto
      rw [untypedRuneToString_ascii 47 (by decide) (by decide)]
      wp_apply _root_.Perennial.strings.wp_Join _ _ dq _ $$ [H2] as H2
      · iframe
      try wp_auto
      wp_apply hClean _ as %r %Hr
      try wp_auto
      ihave Hsl := (ownSlice_slice (V := GoString) (W64 (n : Int)) sl.len sl dq es
        ⟨by word, by word, Int.le_refl _⟩).2 $$ [H1 H2 H3]
      · iframe
      wp_for_post
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      have hsub : subslice (sint.nat (W64 (n : Int))) (sint.nat sl.len) es = es.drop n := by
        rw [show sint.nat (W64 (n : Int)) = n by word,
          show sint.nat sl.len = es.length by have := Hsll.1; omega]
        simp [subslice]
      have hne : es[n] ≠ [] := by
        rw [List.getElem?_eq_getElem hn] at hei; rw [Option.some.inj hei]; exact he
      rw [Hr, hsub, filepath.joinModel_drop es n hn Hemp hne]
  · have hne : n = es.length := by omega
    subst hne
    have hc : ¬ sint.Z (W64 (es.length : Int)) < sint.Z sl.len := by
      have := Hsll.1; word
    rw [if_neg (by rw [decide_eq_true_eq]; exact hc)]
    rw [if_neg (by rw [decide_eq_true_eq]; exact hc)]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    rw [filepath.joinModel_empties es Hemp]

end proof

end EtcdGrove
end Perennial
