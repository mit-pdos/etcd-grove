/-
`MkdirAll`'s `parent` of a path (`os.model.mkdirAllParent`, `TrustedCode/os.lean`) and `model.base`,
the base name a `fileStat` stores (moved here from `MkdirAllParts.lean`, 2026-11-13, for `StatS` and
`File.Stat`). Untrusted.

* `os.parentModel`, `os.model.wp_mkdirAllParent`: `MkdirAll`'s `parent` of any path, and
  `os.parentModel_child`: of `d/b` it is `d`.
* `os.model.wp_base`: `model.base` of any path: some string.
-/
module

public import LinuxFs.Proof.os.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

/-- `MkdirAll`'s `parent` of any path: `os.parentModel`. -/
theorem os.model.wp_mkdirAllParent (p : GoString) :
    {{ (True : IProp GF) }} (App (Val os.model.mkdirAllParent) (Val #p))
    {{ RET #(os.parentModel p); True }} := by
  wp_start
  try unfold os.model.mkdirAllParent
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  obtain ⟨n, hn⟩ : ∃ n : Nat, n = p.length := ⟨_, rfl⟩
  rw [show W64 (p.length : Int) = W64 (n : Int) from by rw [hn]]
  have hT : os.trailIdx p n = os.trailIdx p p.length := by rw [hn]
  have Hn : n ≤ p.length := by omega
  clear hn
  try wp_auto
  iclear Hpre
  iloeb as IH generalizing %n %hT %Hn
  cases n with
  | zero =>
    simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
      _root_.decide_false]
    wp_auto
    have hM : os.parentModel p = List.take (0 - 0) (List.drop 0 p) := by
      unfold os.parentModel; rw [← hT]; simp [os.trailIdx, os.backIdx]
    rw [← hM]
    iapply HΦ
    itrivial
  | succ k =>
    rw [show W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) by word]
    simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) by word, _root_.decide_true]
    wp_auto
    have hk : k < p.length := by omega
    simp only [show (0 : Int) ≤ sint.Z (W64 (k : Int)) by word, ↓reduceIte,
      show sint.nat (W64 (k : Int)) = k by word, List.getElem?_eq_getElem hk]
    try wp_auto
    wp_apply os.wp_IsPathSeparator
    by_cases hs : p[k] = slashB
    · rw [decide_eq_true hs]
      wp_auto
      have hT' : os.trailIdx p k = os.trailIdx p p.length := by
        rw [← hT]; simp only [os.trailIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some, hs, ↓reduceIte]
      iapply IH $$ %k %hT' %(by omega) HΦ
    · rw [decide_eq_false hs]
      wp_auto
      have hT1 : os.trailIdx p (k + 1) = k + 1 := by
        simp only [os.trailIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some, hs, ↓reduceIte]
      have hB : os.backIdx p (k + 1) = os.backIdx p (os.trailIdx p p.length) := by
        rw [← hT, hT1]
      rw [show W64 (k : Int) = W64 ((k + 1 : Nat) : Int) - W64 1 by word]
      generalize k + 1 = m at hB Hn
      clear hT hT1 hk hs
      iclear IH
      iloeb as IH generalizing %m %hB %Hn
      cases m with
      | zero =>
        simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
          _root_.decide_false]
        wp_auto
        have hM : os.parentModel p = List.take (0 - 0) (List.drop 0 p) := by
          unfold os.parentModel; rw [← hB]; simp [os.backIdx]
        rw [← hM]
        iapply HΦ
        itrivial
      | succ k =>
        rw [show W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) by word]
        simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) by word, _root_.decide_true]
        wp_auto
        have hk : k < p.length := by omega
        simp only [show (0 : Int) ≤ sint.Z (W64 (k : Int)) by word, ↓reduceIte,
          show sint.nat (W64 (k : Int)) = k by word, List.getElem?_eq_getElem hk]
        try wp_auto
        wp_apply os.wp_IsPathSeparator
        by_cases hs : p[k] = slashB
        · rw [decide_eq_true hs]
          wp_auto
          simp only [show ¬ sint.Z (W64 (k : Int)) < sint.Z (W64 0) by word, _root_.decide_false]
          wp_auto
          rw [ite_cond_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
          wp_auto
          have hM : os.parentModel p = List.take (sint.nat (W64 (k : Int)) - 0) (List.drop 0 p) := by
            unfold os.parentModel
            rw [← hB]
            simp only [os.backIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
              Option.getD_some, hs, ↓reduceIte, List.drop_zero,
              show sint.nat (W64 (k : Int)) = k by word]
            rfl
          rw [← hM]
          iapply HΦ
          itrivial
        · rw [decide_eq_false hs]
          wp_auto
          have hB' : os.backIdx p k = os.backIdx p (os.trailIdx p p.length) := by
            rw [← hB]; simp only [os.backIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
              Option.getD_some, hs, ↓reduceIte]
          iapply IH $$ %k %hB' %(by omega) HΦ

/-- `model.base` of any path: some string. -/
theorem os.model.wp_base (p : GoString) :
    {{ (True : IProp GF) }} (App (Val os.model.base) (Val #p))
    {{ (s : GoString), RET #s; True }} := by
  wp_start
  try unfold os.model.base
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  try wp_auto
  by_cases h0 : p = []
  · subst h0
    simp only [List.length_nil]
    wp_auto
    iapply HΦ $$ %_
    itrivial
  have hne : W64 (p.length : Int) ≠ W64 0 := by
    have : p.length ≠ 0 := by simpa using h0
    intro h; apply this; word
  rw [decide_eq_false hne]
  wp_auto
  wp_apply os.model.wp_mkdirAllParent
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen2
  have hpl := os.parentModel_length p h0
  try wp_auto
  rw [if_pos (by word)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  wp_if_destruct
  · iapply HΦ $$ %_
    itrivial
  · iapply HΦ $$ %_
    itrivial

end proof

end EtcdGrove
end Perennial
