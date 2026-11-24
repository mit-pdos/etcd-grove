/-
`MkdirAll`'s `parent` of a path (`path.go`; Go's `MkdirAll` is translated since 2026-11-24, Go-model
overlays S5). Untrusted.

* `os.parentModel`: `MkdirAll`'s `parent` of any path; `os.parentModel_child`: of `d/b` it is `d`;
  `os.rootsAbove_parent`: of a root or a strict ancestor of one, a strict ancestor of one (or empty).
* `mkdirall_parent P K`: `MkdirAll`'s two loops, `if i < 0 { i = 0 }` and `parent := path[:i]` on the
  path `P`, ending with `parent ↦ os.parentModel P`, then the tactic `K` (once per exit of the loops).
-/
module

public import Proof.os.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Proof.internal.filepathlite.Lexical
public import GooseLang.Ext.Fs.TreeSharedOut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `MkdirAll`'s first loop, on the length `n` of the prefix left (`i = n - 1`): skip trailing
separators. -/
def os.trailIdx (p : GoString) : Nat → Nat
  | 0 => 0
  | n + 1 => if p.getD n 0 = slashB then os.trailIdx p n else n + 1

/-- `MkdirAll`'s second loop: skip the last component. -/
def os.backIdx (p : GoString) : Nat → Nat
  | 0 => 0
  | n + 1 => if p.getD n 0 = slashB then n + 1 else os.backIdx p n

/-- `MkdirAll`'s `parent` of `p`: up to the last separator before its last component. -/
def os.parentModel (p : GoString) : GoString := p.take (os.backIdx p (os.trailIdx p p.length) - 1)

theorem os.trailIdx_le (p : GoString) (n : Nat) : os.trailIdx p n ≤ n := by
  induction n with
  | zero => simp [os.trailIdx]
  | succ n ih => simp only [os.trailIdx]; split <;> omega

theorem os.backIdx_le (p : GoString) (n : Nat) : os.backIdx p n ≤ n := by
  induction n with
  | zero => simp [os.backIdx]
  | succ n ih => simp only [os.backIdx]; split <;> omega

theorem os.backIdx_child (d b : GoString) (hb : slashB ∉ b) :
    ∀ k ≤ b.length, os.backIdx (child d b) (d.length + 1 + k) = d.length + 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    show os.backIdx (child d b) (d.length + 1) = d.length + 1
    simp [os.backIdx, child, List.getD_eq_getElem?_getD]
  | succ k ih =>
    intro hk
    rw [show d.length + 1 + (k + 1) = (d.length + 1 + k) + 1 by omega]
    simp only [os.backIdx]
    have hkb : k < b.length := by omega
    have hg : (child d b).getD (d.length + 1 + k) 0 = b[k] := by
      simp [child, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        show d.length ≤ d.length + 1 + k by omega, show d.length + 1 + k - d.length = k + 1 by omega,
        List.getElem?_eq_getElem hkb]
    have hne : b[k] ≠ slashB := fun h => hb (h ▸ List.getElem_mem hkb)
    simp only [hg, hne, ↓reduceIte]
    exact ih (by omega)

theorem os.parentModel_child (d b : GoString) (hb : NameOk b) : os.parentModel (child d b) = d := by
  obtain ⟨hne, -, -, hs, -⟩ := hb
  have hlen : (child d b).length = d.length + 1 + b.length := by simp [child]; omega
  obtain ⟨k, hk⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by
    cases b with | nil => exact absurd rfl hne | cons _ _ => simp⟩
  have ht : os.trailIdx (child d b) (child d b).length = (child d b).length := by
    rw [hlen, hk, show d.length + 1 + (k + 1) = (d.length + 1 + k) + 1 by omega]
    simp only [os.trailIdx]
    have hkb : k < b.length := by omega
    have hg : (child d b).getD (d.length + 1 + k) 0 = b[k] := by
      simp [child, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        show d.length ≤ d.length + 1 + k by omega, show d.length + 1 + k - d.length = k + 1 by omega,
        List.getElem?_eq_getElem hkb]
    have hne : b[k] ≠ slashB := fun h => hs (h ▸ List.getElem_mem hkb)
    simp only [hg, hne, ↓reduceIte]
  unfold os.parentModel
  rw [ht, hlen, os.backIdx_child d b hs b.length (Nat.le_refl _)]
  simp [child]

theorem os.parentModel_length (p : GoString) (hp : p ≠ []) :
    (os.parentModel p).length + 1 ≤ p.length := by
  unfold os.parentModel
  have h1 := os.trailIdx_le p p.length
  have h2 := os.backIdx_le p (os.trailIdx p p.length)
  have : p.length ≠ 0 := by simpa using hp
  simp only [List.length_take]
  omega

/-- `backIdx` stops just past a separator, or at 0. -/
theorem os.backIdx_slash (p : GoString) :
    ∀ n, n ≤ p.length → os.backIdx p n = 0 ∨ ∃ k, os.backIdx p n = k + 1 ∧ p[k]? = some slashB
  | 0, _ => by simp [os.backIdx]
  | n + 1, hn => by
    simp only [os.backIdx]
    split
    · next h =>
      right
      refine ⟨n, rfl, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h
      rw [List.getElem?_eq_getElem (by omega)]
      simpa using h
    · exact os.backIdx_slash p n (by omega)

/-- A non-empty `parent` followed by a separator is a prefix of the path. -/
theorem os.parentModel_prefix (p : GoString) (h : os.parentModel p ≠ []) :
    (os.parentModel p ++ [slashB]).IsPrefix p := by
  unfold os.parentModel at *
  rcases os.backIdx_slash p (os.trailIdx p p.length) (os.trailIdx_le p p.length) with h0 | ⟨k, hk, hpk⟩
  · rw [h0] at h; simp at h
  · rw [hk, Nat.add_sub_cancel]
    have : p.take k ++ [slashB] = p.take (k + 1) := by rw [List.take_succ, hpk]; rfl
    rw [this]; exact List.take_prefix _ _

theorem os.parentModel_slash : os.parentModel [slashB] = [] := by
  simp [os.parentModel, os.trailIdx, os.backIdx, List.getD]

/-- The `parent` of a root or of a strict ancestor of one, if not empty, is a strict ancestor of
one. -/
theorem os.rootsAbove_parent {R : Roots} {p : GoString}
    (h : RootsAbove R p ∨ ∃ rj ∈ R, rj.1 = p) (hne : os.parentModel p ≠ []) :
    RootsAbove R (os.parentModel p) := by
  right
  refine ⟨hne, ?_⟩
  have hpp := os.parentModel_prefix p hne
  rcases h with (rfl | ⟨-, rj, hm, hpr⟩) | ⟨rj, hm, rfl⟩
  · exact absurd os.parentModel_slash hne
  · exact ⟨rj, hm, hpp.trans ((List.prefix_append p [slashB]).trans hpr)⟩
  · exact ⟨rj, hm, hpp⟩

/-- `parentModel` of a path of the roots' components: `joinPath r cs`'s is `r`'s components minus
the last (`cs ≠ []`). -/
theorem os.parentModel_joinPath_snoc (r : GoString) (cs : List GoString) (c : GoString) (hc : NameOk c) :
    os.parentModel (joinPath r (cs ++ [c])) = joinPath r cs := by
  rw [joinPath_snoc]; exact os.parentModel_child _ c hc

set_option hygiene false in
/-- `MkdirAll`'s slice `parent := path[:i]` at `i = k` (`hM : os.parentModel P = P.take k`), then `K`. -/
macro "mkdirall_slice " P:term:max k:term:max hM:ident K:tactic : tactic => `(tactic| (
  try wp_auto
  try rw [if_pos (by refine ⟨by word, by word, by word⟩)]
  try wp_auto
  try simp only [show sint.nat (W64 (($k : Nat) : Int)) = $k by word, show sint.nat (W64 0) = 0 from rfl,
    Nat.sub_zero, List.drop_zero]
  (rw [← $hM:ident])
  $K))

set_option hygiene false in
/-- `MkdirAll`'s second loop (`for i >= 0 && !IsPathSeparator(path[i]) { i-- }`) from `i = m0 - 1`
(`hB0`), then `if i < 0 { i = 0 }` and the slice (`mkdirall_slice`), then `K`. -/
macro "mkdirall_loop2 " P:term:max m0:term:max hB0:ident K:tactic : tactic => `(tactic| (
  ihave HB : (∃ (m : Nat), "i" ∷ i_ptr ↦ (W64 (m : Int) - W64 1) ∗
      "%Hm" ∷ ⌜m ≤ ($P).length ∧ os.backIdx $P m = os.backIdx $P (os.trailIdx $P ($P).length)⌝ :
      IProp GF) $$ [i]
  · iexists $m0; iframe; ipureintro; exact ⟨by omega, $hB0:ident⟩
  wp_for HB
  obtain ⟨Hml, Hmb⟩ := Hm
  cases m with
  | zero =>
    simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
      _root_.decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    try wp_auto
    try simp only [show sint.Z (W64 ((0 : Nat) : Int) - W64 1) < sint.Z (W64 0) by decide,
      _root_.decide_true]
    try wp_auto
    have hM : os.parentModel $P = List.take 0 $P := by
      unfold os.parentModel; rw [← Hmb]; simp [os.backIdx]
    mkdirall_slice $P 0 hM $K
  | succ k =>
    have hk : k < ($P).length := by omega
    rw [show W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) by word]
    simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) by word, _root_.decide_true]
    try wp_auto
    simp only [show (0 : Int) ≤ sint.Z (W64 (k : Int)) by word, ↓reduceIte,
      show sint.nat (W64 (k : Int)) = k by word, List.getElem?_eq_getElem hk]
    try wp_auto
    wp_apply os.wp_IsPathSeparatorF
    by_cases hs : ($P)[k] = slashB
    · rw [decide_eq_true hs]
      simp only [Bool.not_true]
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      try wp_auto
      try simp only [show ¬ sint.Z (W64 (k : Int)) < sint.Z (W64 0) by word, _root_.decide_false]
      try wp_auto
      have hM : os.parentModel $P = List.take k $P := by
        unfold os.parentModel
        rw [← Hmb]
        simp only [os.backIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some, hs, ↓reduceIte, Nat.add_sub_cancel]
      mkdirall_slice $P k hM $K
    · rw [decide_eq_false hs]
      simp only [Bool.not_false]
      rw [if_pos (by simp)]
      try wp_auto
      wp_for_post
      iframe
      iexists k
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [← Hmb]
      simp only [os.backIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some, hs, ↓reduceIte]))

set_option hygiene false in
/-- `MkdirAll`'s parent of the path `P` (at `path_ptr`), from `i := len(path) - 1` to
`parent := path[:i]`: `parent ↦ os.parentModel P`, then `K` (once per exit of the loops). -/
macro "mkdirall_parent " P:term:max K:tactic : tactic => `(tactic| (
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hPlen
  try wp_auto
  ihave HT : (∃ (n : Nat), "i" ∷ i_ptr ↦ (W64 (n : Int) - W64 1) ∗
      "%Hn" ∷ ⌜n ≤ ($P).length ∧ os.trailIdx $P n = os.trailIdx $P ($P).length⌝ : IProp GF) $$ [i]
  · iexists ($P).length; iframe; ipureintro; exact ⟨Nat.le_refl _, rfl⟩
  wp_for HT
  obtain ⟨Hnl, Hnt⟩ := Hn
  cases n with
  | zero =>
    simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
      _root_.decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    try wp_auto
    have hB0 : os.backIdx $P 0 = os.backIdx $P (os.trailIdx $P ($P).length) := by
      rw [← Hnt]; simp only [os.trailIdx]
    mkdirall_loop2 $P 0 hB0 $K
  | succ k =>
    have hk : k < ($P).length := by omega
    rw [show W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) by word]
    simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) by word, _root_.decide_true]
    try wp_auto
    simp only [show (0 : Int) ≤ sint.Z (W64 (k : Int)) by word, ↓reduceIte,
      show sint.nat (W64 (k : Int)) = k by word, List.getElem?_eq_getElem hk]
    try wp_auto
    wp_apply os.wp_IsPathSeparatorF
    by_cases hs : ($P)[k] = slashB
    · rw [decide_eq_true hs, if_pos (by simp)]
      try wp_auto
      wp_for_post
      iframe
      iexists k
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [← Hnt]
      simp only [os.trailIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some, hs, ↓reduceIte]
    · rw [decide_eq_false hs]
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      try wp_auto
      have hT1 : os.trailIdx $P (k + 1) = k + 1 := by
        simp only [os.trailIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some, hs, ↓reduceIte]
      have hB0 : os.backIdx $P (k + 1) = os.backIdx $P (os.trailIdx $P ($P).length) := by
        rw [← Hnt, hT1]
      rw [show W64 (k : Int) = W64 ((k + 1 : Nat) : Int) - W64 1 by word]
      mkdirall_loop2 $P (k + 1) hB0 $K))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- `os.IsPathSeparator(c)`: whether `c` is `'/'`. -/
theorem os.wp_IsPathSeparator (c : w8) :
    {{ (True : IProp GF) }} (App (Val #(functions go!"os.IsPathSeparator" [])) (Val #c))
    {{ RET #(decide (c = slashB)); True }} := by
  rw [show (go!"os.IsPathSeparator" : GoString) = os.IsPathSeparator from rfl]
  wp_start
  try wp_auto
  rw [show decide (W8 47 = c) = decide (c = slashB) from decide_eq_decide.mpr eq_comm]
  iapply HΦ
  try itrivial

/-- `os.wp_IsPathSeparator` at the callee as `wp_auto` leaves it (`functions os.IsPathSeparator`). -/
theorem os.wp_IsPathSeparatorF (c : w8) :
    {{ (True : IProp GF) }} (App (Val (@! os.IsPathSeparator)) (Val #c))
    {{ RET #(decide (c = slashB)); True }} :=
  os.wp_IsPathSeparator c

end proof

end EtcdGrove
end Perennial
