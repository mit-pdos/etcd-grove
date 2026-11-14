/-
Proof of `LinuxFs/Spec/internal/filepathlite/Dir.lean` (Go 1.27 `path.go`: the volume name, empty on
Unix; the scan back to the last separator, as `Base`'s; `Clean` of what precedes it). Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.Dir
public import LinuxFs.Spec.internal.filepathlite.Clean
public import LinuxFs.Spec.internal.filepathlite.IsPathSeparator
public import LinuxFs.Spec.internal.filepathlite.VolumeName

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
/-- After `Dir`'s scan loop, `i` at `iv` (`hiv`: the last separator's index in `p`, or `-1`). -/
local macro "dir_tail" : tactic => `(tactic| (
    have hb := path.lastIndexByte_bounds p path.slash
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    try simp only [List.length_nil]
    rw [if_pos (by refine ⟨by word, by word, by word⟩)]
    have htake : List.take (sint.nat (iv + W64 1) - sint.nat (W64 ((0 : Nat) : Int)))
        (List.drop (sint.nat (W64 ((0 : Nat) : Int))) p) =
        p.take (path.lastIndexByte p path.slash + 1).toNat := by
      rw [show sint.nat (iv + W64 1) = (path.lastIndexByte p path.slash + 1).toNat by word,
        show sint.nat (W64 ((0 : Nat) : Int)) = 0 by rfl, Nat.sub_zero, List.drop_zero]
    rw [htake]
    try wp_auto
    wp_apply hClean
    iintro %r %Hr
    subst Hr
    try wp_auto
    have hM : path.dirModel p = path.cleanModel (p.take (path.lastIndexByte p path.slash + 1).toNat) := rfl
    generalize path.cleanModel (p.take (path.lastIndexByte p path.slash + 1).toNat) = c at *
    by_cases hd : c = go!"."
    · simp only [hd, _root_.decide_true]
      try wp_auto
      try wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      iapply HΦ; ipureintro; rw [hM, hd]; rfl
    · rw [decide_eq_false hd]
      try wp_auto
      iapply HΦ; ipureintro; rw [hM]; rfl))

theorem filepathlite.Dir.wp_proof
    (hVol : filepathlite.VolumeName.spec (GF := GF) (hG := hG))
    (hSep : filepathlite.IsPathSeparator.spec (GF := GF) (hG := hG))
    (hClean : filepathlite.Clean.spec (GF := GF) (hG := hG)) :
    filepathlite.Dir.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_apply hVol
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hplen
  try wp_auto
  ihave HJ : (∃ (k : Nat), "i" ∷ i_ptr ↦ (W64 (k : Int) - W64 1) ∗
      "%Hk" ∷ ⌜k ≤ p.length ∧ path.lastIdxFrom p path.slash k = path.lastIndexByte p path.slash⌝ :
      IProp GF) $$ [i]
  · iexists p.length
    iframe
    ipureintro; exact ⟨Nat.le_refl _, rfl⟩
  wp_for HJ
  obtain ⟨Hkl, Hli⟩ := Hk
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  simp only [List.length_nil]
  cases k with
  | zero =>
    simp only [show ¬ sint.Z (W64 ((0 : Nat) : Int) - W64 1) ≥ sint.Z (W64 ((0 : Nat) : Int)) by decide,
      _root_.decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    have hiv : sint.Z (W64 ((0 : Nat) : Int) - W64 1) = path.lastIndexByte p path.slash := by
      rw [← Hli]; rfl
    generalize W64 ((0 : Nat) : Int) - W64 1 = iv at *
    dir_tail
  | succ j =>
    have hj : j < p.length := by omega
    rw [show W64 ((j + 1 : Nat) : Int) - W64 1 = W64 (j : Int) by word]
    simp only [show sint.Z (W64 ((0 : Nat) : Int)) ≤ sint.Z (W64 (j : Int)) by word, _root_.decide_true]
    try wp_auto
    obtain ⟨c, hpc⟩ : ∃ c, p[j]? = some c := ⟨_, List.getElem?_eq_getElem hj⟩
    have hgc : p.getD j 0 = c := by simp [List.getD, hpc]
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
      have hiv : sint.Z (W64 (j : Int)) = path.lastIndexByte p path.slash := by
        rw [← Hli, path.lastIdxFrom, if_pos (hgc.trans hs)]; word
      generalize W64 (j : Int) = iv at *
      dir_tail
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
      rw [← Hli, path.lastIdxFrom, if_neg (hgc ▸ hs)]

end proof

end EtcdGrove
end Perennial
