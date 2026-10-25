/-
Proof of `Spec/path/Base.lean`. Lean-first.
-/
module

public import Spec.path.Base
public import Spec.internal.bytealg.LastIndexByteString

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.path.Assumptions]

/-- A loop's condition that is `false`: the loop ends. -/
local macro "cond_false" : tactic => `(tactic|
  rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
    if_pos (by simp)])

/-- A loop's condition that is `true`: the body runs. -/
local macro "cond_true" : tactic => `(tactic| rw [if_pos (by simp)])

set_option hygiene false in
/-- After the loop, at `q` (`Hqs : stripSlashes p = q`): the last element of `q`, `"/"` if empty. -/
local macro "base_tail" q:term : tactic => `(tactic| (
  try wp_auto
  wp_apply hLast $q (W8 47) as %Hl2
  have hb := path.lastIndexByte_bounds $q (W8 47)
  try wp_auto
  wp_if_destruct
  · -- the last `/`'s index `i ≥ 0`: the rest after it
    have hi0 : 0 ≤ path.lastIndexByte $q (W8 47) := by revert Hif; word
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    have h1 : sint.Z (W64 (path.lastIndexByte $q (W8 47)) + W64 1) =
        path.lastIndexByte $q (W8 47) + 1 := by word
    have h3 : sint.Z (W64 (($q).length : Int)) = ($q).length := by word
    rw [if_pos (by rw [h1, h3]; refine ⟨by omega, by omega, by word⟩)]
    try wp_auto
    have h2 : sint.nat (W64 (path.lastIndexByte $q (W8 47)) + W64 1) =
        (path.lastIndexByte $q (W8 47) + 1).toNat := by word
    have h4 : sint.nat (W64 (($q).length : Int)) = ($q).length := by word
    simp only [h2, h4]
    rw [List.take_of_length_le (l := List.drop _ $q) (by simp)]
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      ipureintro
      unfold path.baseModel
      simp only [show (W8 47 : w8) = 47#8 from rfl] at *
      simp [Hpne, Hqs, hi0, *]
    · try wp_auto
      iapply HΦ
      ipureintro
      unfold path.baseModel
      simp only [show (W8 47 : w8) = 47#8 from rfl] at *
      simp [Hpne, Hqs, hi0, *]
  · have hi0 : ¬ 0 ≤ path.lastIndexByte $q (W8 47) := by revert Hif; word
    try wp_auto
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      ipureintro
      unfold path.baseModel
      simp only [show (W8 47 : w8) = 47#8 from rfl] at *
      simp [Hpne, Hqs, hi0, *]
    · try wp_auto
      iapply HΦ
      ipureintro
      unfold path.baseModel
      simp only [show (W8 47 : w8) = 47#8 from rfl] at *
      simp [Hpne, Hqs, hi0, *]))

theorem path.Base.wp_proof (hLast : bytealg.LastIndexByteString.spec (GF := GF) (hG := hG)) :
    path.Base.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  ihave #Hb : isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg $$ []
  · iPkgInit
  try wp_auto
  wp_if_destruct
  · -- `""`
    try wp_auto
    iapply HΦ; ipureintro; rfl
  try wp_auto
  have Hpne : p ≠ [] := Hif
  ihave HI : (∃ q : GoString, "path" ∷ path_ptr ↦ q ∗
      "%Hq" ∷ ⌜path.stripSlashes q = path.stripSlashes p⌝ : IProp GF) $$ [path]
  · iexists p; iframe; ipureintro; rfl
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hql
  rcases List.eq_nil_or_concat q with rfl | ⟨q', x, rfl⟩
  · -- empty: the loop ends
    try wp_auto
    cond_false
    have Hqs : path.stripSlashes p = [] := by rw [← Hq]; rfl
    try wp_auto
    wp_apply hLast [] (W8 47) as %-
    try wp_auto
    iapply HΦ
    ipureintro
    unfold path.baseModel
    simp [Hpne, Hqs, path.lastIndexByte, path.lastIdxFrom]
  · simp only [List.concat_eq_append] at *
    try wp_auto
    wp_if_destruct
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      have hi : sint.nat (W64 ((q' ++ [x]).length : Int) - W64 1) = q'.length := by
        simp only [List.length_append, List.length_singleton] at Hql ⊢; word
      have hi0 : 0 ≤ sint.Z (W64 ((q' ++ [x]).length : Int) - W64 1) := by
        simp only [List.length_append, List.length_singleton] at Hql ⊢; word
      simp only [hi, hi0, ↓reduceIte, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
      try wp_auto
      by_cases hx : x = W8 47
      · subst hx
        rw [if_pos (by simp)]
        try wp_auto
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
        rw [if_pos (by simp only [List.length_append, List.length_singleton] at Hql ⊢; word)]
        try wp_auto
        wp_for_post
        iframe
        iexists q'
        have ht : List.take q'.length (q' ++ [W8 47]) = q' := by simp
        simp only [hi, Nat.sub_zero, List.drop_zero, ht]
        iframe
        ipureintro
        rw [← Hq, path.stripSlashes_snoc_slash]
      · rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact hx (by simpa using go.intoVal_inj h)),
          if_pos (by rw [decide_eq_false hx]; simp)]
        have Hqs : path.stripSlashes p = q' ++ [x] := by rw [← Hq, path.stripSlashes_snoc_ne _ _ hx]
        base_tail (q' ++ [x])
    · exfalso; apply Hif; simp only [List.length_append, List.length_singleton] at Hql ⊢; word

end proof

end EtcdGrove
end Perennial
