/-
Proof of `LinuxFs/Spec/internal/filepathlite/Ext.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.Ext
public import LinuxFs.Spec.internal.filepathlite.IsPathSeparator

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

theorem filepathlite.Ext.wp_proof
    (hSep : filepathlite.IsPathSeparator.spec (GF := GF) (hG := hG)) :
    filepathlite.Ext.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hpl
  try wp_auto
  ihave HI : (∃ (k : Nat), "i" ∷ i_ptr ↦ (W64 (k : Int) - W64 1) ∗
      "%Hk" ∷ ⌜k ≤ p.length ∧ filepath.extFrom p k = filepath.extModel p⌝ : IProp GF) $$ [i]
  · iexists p.length
    iframe
    ipureintro; exact ⟨Nat.le_refl _, rfl⟩
  wp_for HI
  obtain ⟨Hkl, Hext⟩ := Hk
  cases k with
  | zero =>
    simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
      decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    try wp_auto
    iapply HΦ; ipureintro; rw [← Hext]; rfl
  | succ j =>
    have hj : j < p.length := by omega
    rw [show W64 ((j + 1 : Nat) : Int) - W64 1 = W64 (j : Int) by word]
    simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (j : Int)) by word, decide_true]
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
      try wp_auto
      iapply HΦ; ipureintro
      rw [← Hext, filepath.extFrom, if_pos (hgc.trans hs)]
    · rw [decide_eq_false hs]
      simp only [Bool.not_false]
      rw [if_pos (by simp)]
      try wp_auto
      simp only [show (0 : Int) ≤ sint.Z (W64 (j : Int)) by word, ↓reduceIte,
        show sint.nat (W64 (j : Int)) = j by word, hpc]
      try wp_auto
      by_cases hd : c = W8 46
      · rw [decide_eq_true hd]
        try wp_auto
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
        try wp_auto
        try rw [if_pos (by refine ⟨by word, by word, by word⟩)]
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ; ipureintro
        rw [← Hext, filepath.extFrom, if_neg (hgc ▸ hs), if_pos (hgc.trans hd)]
        simp only [show sint.nat (W64 (j : Int)) = j by word,
          show sint.nat (W64 (p.length : Int)) = p.length by word]
        exact List.take_of_length_le (by simp)
      · rw [decide_eq_false hd]
        try wp_auto
        wp_for_post
        iframe
        iexists j
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        rw [← Hext, filepath.extFrom, if_neg (hgc ▸ hs), if_neg (hgc ▸ hd)]

end proof

end EtcdGrove
end Perennial
