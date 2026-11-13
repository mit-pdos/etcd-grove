/-
Proof of `LinuxFs/Spec/internal/filepathlite/Base.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.Base
public import LinuxFs.Spec.internal.filepathlite.IsPathSeparator
public import LinuxFs.Spec.internal.filepathlite.VolumeName
public import LinuxFs.Proof.internal.filepathlite.UntypedRune

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.filepathlite.Assumptions]

set_option hygiene false in
/-- The end of `Base`: `"/"` if what is left is empty (`hM`: the model's result from `Q`). -/
local macro "base_fin" Q:term:max : tactic => `(tactic| (
  by_cases hQ : $Q = []
  · simp only [hQ, _root_.decide_true]
    try wp_auto
    try simp only [_root_.Perennial.internal.filepathlite.Separator]
    try wp_auto
    iapply HΦ; ipureintro
    rw [hM, if_pos hQ, untypedRuneToString_ascii 47 (by decide) (by decide)]; try decide
  · simp only [hQ, _root_.decide_false]
    try wp_auto
    iapply HΦ; ipureintro; rw [hM, if_neg hQ]))

set_option hygiene false in
/-- After `Base`'s scan loop, `i` at `iv` (`hiv`: the last slash's index in `q`, the path without
its trailing slashes, `Hqe`). -/
local macro "base_tail" : tactic => `(tactic| (
  have hb := path.lastIndexByte_bounds q path.slash
  try wp_auto
  by_cases hge : 0 ≤ path.lastIndexByte q path.slash
  · simp only [show sint.Z (W64 0) ≤ sint.Z iv by word, _root_.decide_true]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    rw [if_pos (by refine ⟨by word, by word, by word⟩)]
    try wp_auto
    have hdrop : List.take (sint.nat (W64 (q.length : Int)) - sint.nat (iv + W64 1))
        (List.drop (sint.nat (iv + W64 1)) q) =
        q.drop (path.lastIndexByte q path.slash + 1).toNat := by
      rw [show sint.nat (iv + W64 1) = (path.lastIndexByte q path.slash + 1).toNat by word,
        show sint.nat (W64 (q.length : Int)) = q.length by word]
      exact List.take_of_length_le (by simp <;> omega)
    rw [hdrop]
    have hM : path.baseModel p = if q.drop (path.lastIndexByte q path.slash + 1).toNat = []
        then go!"/" else q.drop (path.lastIndexByte q path.slash + 1).toNat := by
      simp only [path.baseModel, Hpne, ↓reduceIte, ← Hqe, hge]
    base_fin (q.drop (path.lastIndexByte q path.slash + 1).toNat)
  · simp only [show ¬ sint.Z (W64 0) ≤ sint.Z iv by word, _root_.decide_false]
    try wp_auto
    have hM : path.baseModel p = if q = [] then go!"/" else q := by
      simp only [path.baseModel, Hpne, ↓reduceIte, ← Hqe, hge]
    base_fin q))

set_option hygiene false in
/-- After `Base`'s strip loop, the path at `q` (`Hqe`: the path without its trailing slashes). -/
local macro "base_after_strip" : tactic => `(tactic| (
  wp_apply hVol
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hqlen
  try wp_auto
  simp only [List.length_nil]
  rw [if_pos (by refine ⟨by word, by word, by word⟩)]
  try wp_auto
  simp only [ show sint.nat (W64 ((0 : Nat) : Int)) = 0 by rfl, Nat.sub_zero,
    List.drop_zero, show sint.nat (W64 (q.length : Int)) = q.length by word, List.take_length]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  ihave HJ : (∃ (k : Nat), "i" ∷ i_ptr ↦ (W64 (k : Int) - W64 1) ∗
      "%Hk" ∷ ⌜k ≤ q.length ∧ path.lastIdxFrom q path.slash k = path.lastIndexByte q path.slash⌝ :
      IProp GF) $$ [i]
  · iexists q.length
    iframe
    ipureintro; exact ⟨Nat.le_refl _, rfl⟩
  wp_for HJ
  obtain ⟨Hkl, Hli⟩ := Hk
  cases k with
  | zero =>
    simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
      _root_.decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    have hiv : sint.Z (W64 ((0 : Nat) : Int) - W64 1) = path.lastIndexByte q path.slash := by
      rw [← Hli]; rfl
    generalize W64 ((0 : Nat) : Int) - W64 1 = iv at *
    base_tail
  | succ j =>
    have hj : j < q.length := by omega
    rw [show W64 ((j + 1 : Nat) : Int) - W64 1 = W64 (j : Int) by word]
    simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (j : Int)) by word, _root_.decide_true]
    try wp_auto
    obtain ⟨c, hpc⟩ : ∃ c, q[j]? = some c := ⟨_, List.getElem?_eq_getElem hj⟩
    have hgc : q.getD j 0 = c := by simp [List.getD, hpc]
    simp only [show (0 : Int) ≤ sint.Z (W64 (j : Int)) by word, ↓reduceIte,
      show sint.nat (W64 (j : Int)) = j by word, hpc]
    try wp_auto
    wp_apply hSep
    try wp_auto
    by_cases hs : c = W8 47
    · rw [decide_eq_true hs]
      simp only [Bool.not_true]
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      have hiv : sint.Z (W64 (j : Int)) = path.lastIndexByte q path.slash := by
        rw [← Hli, path.lastIdxFrom, if_pos (hgc.trans hs)]; word
      generalize W64 (j : Int) = iv at *
      base_tail
    · rw [decide_eq_false hs]
      simp only [Bool.not_false]
      rw [if_pos (by simp)]
      try wp_auto
      wp_for_post
      iframe
      iexists j
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [← Hli, path.lastIdxFrom, if_neg (hgc ▸ hs)]))

theorem filepathlite.Base.wp_proof [UntypedRuneSemantics]
    (hSep : filepathlite.IsPathSeparator.spec (GF := GF) (hG := hG))
    (hVol : filepathlite.VolumeName.spec (GF := GF) (hG := hG)) :
    filepathlite.Base.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; ipureintro; simp [path.baseModel]
  have Hpne : p ≠ [] := Hif
  ihave HS : (∃ (q : GoString), "path" ∷ path_ptr ↦ q ∗
      "%Hq" ∷ ⌜q.length ≤ p.length ∧ path.stripSlashes q = path.stripSlashes p⌝ : IProp GF) $$ [path]
  · iexists p
    iframe
    ipureintro; exact ⟨Nat.le_refl _, rfl⟩
  wp_for HS
  obtain ⟨Hql, Hqs⟩ := Hq
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hqlen
  try wp_auto
  by_cases hq0 : q = []
  · simp only [show ¬ sint.Z (W64 0) < sint.Z (W64 (q.length : Int)) by rw [hq0]; decide,
      _root_.decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    try wp_auto
    have Hqe : q = path.stripSlashes p := by rw [← Hqs, hq0]; rfl
    clear Hqs Hql
    base_after_strip
    
  · have hql : 0 < q.length := List.length_pos_iff.mpr hq0
    obtain ⟨c, hc⟩ : ∃ c, q[q.length - 1]? = some c := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hsnoc : q.take (q.length - 1) ++ [c] = q := by
      have h := List.dropLast_concat_getLast hq0
      rw [List.dropLast_eq_take, List.getLast_eq_getElem] at h
      rw [List.getElem?_eq_getElem (by omega)] at hc
      rw [← Option.some.inj hc]; exact h
    simp only [show sint.Z (W64 0) < sint.Z (W64 (q.length : Int)) by word, _root_.decide_true]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    rw [show W64 (q.length : Int) - W64 1 = W64 ((q.length - 1 : Nat) : Int) by word]
    simp only [show (0 : Int) ≤ sint.Z (W64 ((q.length - 1 : Nat) : Int)) by word, ↓reduceIte,
      show sint.nat (W64 ((q.length - 1 : Nat) : Int)) = q.length - 1 by word, hc]
    try wp_auto
    wp_apply hSep
    try wp_auto
    by_cases hs : c = W8 47
    · rw [decide_eq_true hs, if_pos (by simp)]
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      rw [if_pos (by refine ⟨by word, by word, by word⟩)]
      try wp_auto
      wp_for_post
      iframe
      iexists q.take (q.length - 1)
      simp only [show sint.nat (W64 0) = 0 by rfl, Nat.sub_zero, List.drop_zero,
        show sint.nat (W64 (q.length : Int) - W64 1) = q.length - 1 by word]
      iframe
      ipureintro
      refine ⟨by simp; omega, ?_⟩
      rw [← Hqs]; conv => rhs; rw [← hsnoc, hs, path.stripSlashes_snoc_slash]
    · rw [decide_eq_false hs]
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      try wp_auto
      have Hqe : q = path.stripSlashes p := by
        rw [← Hqs]; conv => rhs; rw [← hsnoc, path.stripSlashes_snoc_ne _ _ hs, hsnoc]
      clear hsnoc hc hs Hqs Hql c
      base_after_strip

end proof

end EtcdGrove
end Perennial
