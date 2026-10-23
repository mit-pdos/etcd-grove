/-
Proof of `Spec/path/Clean.lean`. Lean-first; the lazy buffer: `Proof/path/Defs.lean`.
-/
module

public import Spec.path.Clean
public import Spec.path.lazybuf__index
public import Spec.path.lazybuf__append
public import Spec.path.lazybuf__string

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

/-- `Clean`'s loop invariant, pure part: the bounds (the output never passes the read index; it
is behind it at an element's start, or at its start position), and the model's run from here
gives the final output `F`. -/
def path.cleanInv (p : List w8) (rt : Bool) (F : List w8) (r dd w : Nat) (P : List w8) : Prop :=
  w ≤ r ∧ r ≤ p.length ∧ dd ≤ w ∧ P.length = p.length ∧
  (w = (if rt then 1 else 0) ∨ w < r ∨ r = p.length ∨ p.getD r 0 = path.slash) ∧
  (rt = true → 1 ≤ dd) ∧ path.cleanLoop p rt r (P.take w) dd = F

set_option hygiene false in
/-- The end of the main loop's round at `(r', dd, w', P')`, `Hrun'` its model run: the invariant. -/
local macro "outer_post" r':term:max w':term:max P':term:max : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists $r', dd, $w', $P'
  iframe
  ipureintro))

set_option hygiene false in
/-- The copy of a real element (`for ; r < n && path[r] != '/'; r++ { out.append(path[r]) }`), from
the output `P1.take w1` (`H1`), then the main loop's next round (`Hrun'`: the model's run from the
copy's end gives `F`). -/
local macro "copy_loop" P1:term:max w1:term:max : tactic => `(tactic| (
  rw [← H1.1] at Hrun'
  ihave HK : (∃ (r' w' : Nat) (P' : List w8), "r" ∷ r_ptr ↦ W64 (r' : Int) ∗
      "Hlb" ∷ path.lbOwn out_ptr p P' w' ∗
      "%Hk" ∷ ⌜w' ≤ r' ∧ r' ≤ p.length ∧ dd ≤ w' ∧ P'.length = p.length ∧
        path.copyElem p r' (P'.take w') = path.copyElem p r (($P1).take $w1)⌝ : IProp GF) $$ [r Hlb]
  · iexists r, $w1, $P1
    iframe
    ipureintro; exact ⟨by omega, by omega, H1.2.2.1, H1.2.2.2, rfl⟩
  wp_for HK
  obtain ⟨Hk1, Hk2, Hk3, Hk4, Hk5⟩ := Hk
  have hr'63 : r' < 2 ^ 63 := by omega
  have hzr' : sint.Z (W64 (r' : Int)) = r' := by word
  have hnr' : sint.nat (W64 (r' : Int)) = r' := by word
  by_cases hr' : r' < p.length
  · obtain ⟨c', hpc'⟩ : ∃ c, p[r']? = some c := ⟨_, List.getElem?_eq_getElem hr'⟩
    have hgc' : p.getD r' 0 = c' := by simp [List.getD, hpc']
    have hc' : sint.Z (W64 (r' : Int)) < sint.Z (W64 (p.length : Int)) := by omega
    simp only [hc', _root_.decide_true]
    try wp_auto
    simp only [show (0 : Int) ≤ sint.Z (W64 (r' : Int)) by omega, ↓reduceIte, hnr', hpc']
    try wp_auto
    by_cases hs' : c' = W8 47
    · -- the element's end: the main loop goes on
      rw [decide_eq_true hs']
      simp only [Bool.not_true]
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      try wp_auto
      rw [path.copyElem_stop p r' _ (by rw [hgc', hs']; simp)] at Hk5
      rw [← Hk5] at Hrun'
      outer_post r' w' P'
      exact ⟨Hk1, Hk2, Hk3, Hk4, Or.inr (Or.inr (Or.inr (by rw [hgc', hs']))), Hrt1, Hrun'.symm⟩
    · rw [decide_eq_false hs']
      simp only [Bool.not_false]
      rw [if_pos (by simp)]
      try wp_auto
      simp only [show (0 : Int) ≤ sint.Z (W64 (r' : Int)) by omega, ↓reduceIte, hnr', hpc']
      try wp_auto
      wp_apply hAppend out_ptr p P' w' c' (by omega) $$ [Hlb] as ⟨%P'', Hlb, %HP''⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists r' + 1, w' + 1, P''
      rw [show W64 ((r' + 1 : Nat) : Int) = W64 (r' : Int) + W64 1 by word]
      iframe
      ipureintro
      refine ⟨by omega, by omega, by omega, HP''.2, ?_⟩
      rw [HP''.1, ← Hk5, path.copyElem_step p r' (P'.take w') hr' (by rw [hgc']; exact hs'), hgc']
  · have hc' : ¬ sint.Z (W64 (r' : Int)) < sint.Z (W64 (p.length : Int)) := by omega
    simp only [hc', _root_.decide_false]
    try wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
      if_pos (by simp)]
    try wp_auto
    rw [path.copyElem_stop p r' _ (by omega)] at Hk5
    rw [← Hk5] at Hrun'
    outer_post r' w' P'
    exact ⟨Hk1, Hk2, Hk3, Hk4, Or.inr (Or.inr (Or.inl (by omega))), Hrt1, Hrun'.symm⟩))

set_option hygiene false in
/-- A `.` element (`Hst2`: the model's step reads one byte): `r++`, the next round. -/
local macro "case_dot" : tactic => `(tactic| (
  try wp_auto
  rw [Hst2] at Hrun'
  wp_for_post
  iframe
  iexists r + 1, dd, w, P
  rw [show W64 ((r + 1 : Nat) : Int) = W64 (r : Int) + W64 1 by word]
  iframe
  ipureintro
  exact ⟨by omega, by omega, Hdw, HPl, Or.inr (Or.inl (by omega)), Hrt1, Hrun'.symm⟩))

set_option hygiene false in
/-- A `..` element (`Hrun'`: the model's step for it; `H3`: what follows it is the end or a
slash): `r += 2`; backtracking to the last slash past `dotdot`, or (not rooted) `..` appended. -/
local macro "case_dotdot" : tactic => `(tactic| (
  ihave ⟨Hwf, %Hwb, Hcl⟩ := path.lbOwn_w $$ Hlb
  have hwl : (P.take w).length = w := by simp; omega
  rw [hwl] at Hrun'
  try wp_auto
  have hw63 : w < 2 ^ 63 := by omega
  have hdd63 : dd < 2 ^ 63 := by omega
  have hzw : sint.Z (W64 (w : Int)) = w := by word
  have hzd : sint.Z (W64 (dd : Int)) = dd := by word
  by_cases hgt : dd < w
  · -- backtracking: `w--`, then down to the last slash past `dotdot`
    simp only [if_pos hgt] at Hrun'
    try dsimp only at Hrun'
    have hc : sint.Z (W64 (dd : Int)) < sint.Z (W64 (w : Int)) := by omega
    simp only [hc, _root_.decide_true]
    try wp_auto
    ihave HJ : (∃ k : Nat, "Hwf" ∷ out_ptr.[_root_.Perennial.path.lazybuf, go!"w"] ↦ W64 (k : Int) ∗
        "Hcl" ∷ (∀ w' : Nat, ⌜w' ≤ p.length⌝ -∗
          out_ptr.[_root_.Perennial.path.lazybuf, go!"w"] ↦ W64 (w' : Int) -∗ path.lbOwn out_ptr p P w') ∗
        "%Hk" ∷ ⌜dd ≤ k ∧ k < w ∧ path.backW (P.take w) dd k = path.backW (P.take w) dd (w - 1)⌝ :
        IProp GF) $$ [Hwf Hcl]
    · iexists w - 1
      rw [show W64 ((w - 1 : Nat) : Int) = W64 (w : Int) - W64 1 by word]
      iframe
      ipureintro; exact ⟨by omega, by omega, rfl⟩
    wp_for HJ
    obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
    have hzk : sint.Z (W64 (k : Int)) = k := by word
    have hgk : (P.take w).getD k 0 = P.getD k 0 := by
      simp [List.getD, List.getElem?_take, Hk2]
    have hkt : (P.take w).take k = P.take k := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    by_cases hkd : dd < k
    · simp only [show sint.Z (W64 (dd : Int)) < sint.Z (W64 (k : Int)) by omega, _root_.decide_true]
      try wp_auto
      ihave Hlb := Hcl $$ %k %(by omega) Hwf
      wp_apply hIndex out_ptr p P k k (by omega) $$ [Hlb] as Hlb
      · iframe
      ihave ⟨Hwf, %Hwb', Hcl⟩ := path.lbOwn_w $$ Hlb
      try wp_auto
      by_cases hsk : P.getD k 0 = W8 47
      · -- the slash: the loop ends at `k`
        rw [decide_eq_true hsk]
        simp only [Bool.not_true]
        rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
          if_pos (by simp)]
        try wp_auto
        have hbw : path.backW (P.take w) dd k = k :=
          path.backW_stop _ _ _ (by rw [hgk]; intro h; exact h.2 hsk)
        rw [← Hk3, hbw, hkt] at Hrun'
        ihave Hlb := Hcl $$ %k %(by omega) Hwf
        wp_for_post
        iframe
        iexists r + 2, dd, k, P
        rw [show W64 ((r + 2 : Nat) : Int) = W64 (r : Int) + W64 2 by word]
        iframe
        ipureintro
        exact ⟨by omega, by omega, Hk1, HPl, Or.inr (Or.inl (by omega)), Hrt1, Hrun'.symm⟩
      · rw [decide_eq_false hsk]
        simp only [Bool.not_false]
        rw [if_pos (by simp)]
        try wp_auto
        wp_for_post
        iframe
        iexists k - 1
        rw [show W64 ((k - 1 : Nat) : Int) = W64 (k : Int) - W64 1 by word]
        iframe
        ipureintro
        refine ⟨by omega, by omega, ?_⟩
        rw [← Hk3]
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [path.backW_step _ _ _ ⟨hkd, by rw [hgk]; exact hsk⟩]
        simp
    · -- `dotdot` reached: the loop ends at `k = dotdot`
      simp only [show ¬ sint.Z (W64 (dd : Int)) < sint.Z (W64 (k : Int)) by omega, _root_.decide_false]
      try wp_auto
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      try wp_auto
      have hbw : path.backW (P.take w) dd k = k :=
        path.backW_stop _ _ _ (by intro h; exact hkd h.1)
      rw [← Hk3, hbw, hkt] at Hrun'
      ihave Hlb := Hcl $$ %k %(by omega) Hwf
      wp_for_post
      iframe
      iexists r + 2, dd, k, P
      rw [show W64 ((r + 2 : Nat) : Int) = W64 (r : Int) + W64 2 by word]
      iframe
      ipureintro
      exact ⟨by omega, by omega, Hk1, HPl, Or.inr (Or.inl (by omega)), Hrt1, Hrun'.symm⟩
  · simp only [if_neg hgt] at Hrun'
    have hc : ¬ sint.Z (W64 (dd : Int)) < sint.Z (W64 (w : Int)) := by omega
    simp only [hc, _root_.decide_false]
    try wp_auto
    cases rt with
    | true =>
      -- rooted: `..` at the root is dropped
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at Hrun'
      simp only [Bool.not_true, Bool.true_eq_false, _root_.decide_false]
      try wp_auto
      ihave Hlb := Hcl $$ %w %Hwb.1 Hwf
      wp_for_post
      iframe
      iexists r + 2, dd, w, P
      rw [show W64 ((r + 2 : Nat) : Int) = W64 (r : Int) + W64 2 by word]
      iframe
      ipureintro
      exact ⟨by omega, by omega, Hdw, HPl, Or.inr (Or.inl (by omega)), Hrt1, Hrun'.symm⟩
    | false =>
      -- not rooted: `..` appended, after a slash if the output is not empty
      simp only [Bool.not_false, ↓reduceIte] at Hrun'
      simp only [Bool.not_false, _root_.decide_true]
      try wp_auto
      have hdw : dd = w := by omega
      by_cases hw0 : w = 0
      · subst hw0
        simp only [show ¬ sint.Z (W64 0) < sint.Z (W64 ((0 : Nat) : Int)) by decide, _root_.decide_false]
        try wp_auto
        ihave Hlb := Hcl $$ %0 %Hwb.1 Hwf
        wp_apply hAppend out_ptr p P 0 (W8 46) (by omega) $$ [Hlb] as ⟨%P1, Hlb, %HP1⟩
        · iframe
        try wp_auto
        wp_apply hAppend out_ptr p P1 1 (W8 46) (by omega) $$ [Hlb] as ⟨%P2, Hlb, %HP2⟩
        · iframe
        ihave ⟨Hwf, %Hwb2, Hcl⟩ := path.lbOwn_w $$ Hlb
        try wp_auto
        ihave Hlb := Hcl $$ %2 %Hwb2.1 Hwf
        have Ho : P2.take 2 = [path.dot, path.dot] := by
          rw [HP2.1, HP1.1]; try simp
        simp only [show ¬ (0 < 0) by decide, ↓reduceIte, List.take_zero, List.nil_append,
          List.length_cons, List.length_nil] at Hrun'
        rw [← Ho] at Hrun'
        wp_for_post
        iframe
        iexists r + 2, 2, 2, P2
        rw [show W64 ((r + 2 : Nat) : Int) = W64 (r : Int) + W64 2 by word]
        iframe
        ipureintro
        exact ⟨by omega, by omega, Nat.le_refl _, HP2.2, Or.inr (Or.inr H3.2.2), by simp,
          Hrun'.symm⟩
      · have hwr : w < r := by
          rcases Hdisj with h | h | h | h
          · exact absurd h (by simpa using hw0)
          · exact h
          · omega
          · exact absurd h hn1
        simp only [show sint.Z (W64 0) < sint.Z (W64 (w : Int)) by word, _root_.decide_true]
        try wp_auto
        ihave Hlb := Hcl $$ %w %Hwb.1 Hwf
        wp_apply hAppend out_ptr p P w (W8 47) (by omega) $$ [Hlb] as ⟨%P1, Hlb, %HP1⟩
        · iframe
        try wp_auto
        wp_apply hAppend out_ptr p P1 (w + 1) (W8 46) (by omega) $$ [Hlb] as ⟨%P2, Hlb, %HP2⟩
        · iframe
        try wp_auto
        wp_apply hAppend out_ptr p P2 (w + 1 + 1) (W8 46) (by omega) $$ [Hlb] as ⟨%P3, Hlb, %HP3⟩
        · iframe
        ihave ⟨Hwf, %Hwb3, Hcl⟩ := path.lbOwn_w $$ Hlb
        try wp_auto
        ihave Hlb := Hcl $$ %(w + 1 + 1 + 1) %Hwb3.1 Hwf
        have Ho : P3.take (w + 1 + 1 + 1) = P.take w ++ [path.slash] ++ [path.dot, path.dot] := by
          rw [HP3.1, HP2.1, HP1.1]; try simp
        simp only [show 0 < w by omega, ↓reduceIte] at Hrun'
        rw [show (P.take w ++ [path.slash] ++ [path.dot, path.dot]).length = w + 1 + 1 + 1 by
          simp [hwl]; try omega] at Hrun'
        rw [← Ho] at Hrun'
        wp_for_post
        iframe
        iexists r + 2, w + 1 + 1 + 1, w + 1 + 1 + 1, P3
        rw [show W64 ((r + 2 : Nat) : Int) = W64 (r : Int) + W64 2 by word]
        iframe
        ipureintro
        exact ⟨by omega, by omega, Nat.le_refl _, HP3.2, Or.inr (Or.inr H3.2.2), by simp,
          Hrun'.symm⟩))

set_option hygiene false in
/-- The real-element case, from its start (`Hrun'`: the model's step is a copy after a slash if
the output is past its start): the slash, then `copy_loop`. -/
local macro "case_default" : tactic => `(tactic| (
  ihave ⟨Hwf, %Hwb, Hcl⟩ := path.lbOwn_w $$ Hlb
  have hwl : (P.take w).length = w := by simp; omega
  rw [hwl] at Hrun'
  by_cases hb : w = (if rt then 1 else 0)
  · -- at the output's start: no slash
    rw [if_neg (by cases rt <;> simp_all)] at Hrun'
    have H1 : P.take w = P.take w ∧ w ≤ r ∧ dd ≤ w ∧ P.length = p.length :=
      ⟨rfl, Hwr, Hdw, HPl⟩
    cases rt with
    | true =>
      simp only [↓reduceIte] at hb
      subst hb
      try wp_auto
      ihave Hlb := Hcl $$ %1 %Hwb.1 Hwf
      copy_loop P 1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hb
      subst hb
      try wp_auto
      ihave Hlb := Hcl $$ %0 %Hwb.1 Hwf
      copy_loop P 0
  · -- past it: a slash first
    rw [if_pos (by cases rt <;> simp_all)] at Hrun'
    have hwr : w < r := by
      rcases Hdisj with h | h | h | h
      · exact absurd h hb
      · exact h
      · omega
      · exact absurd (hgc ▸ h) h1
    have hb' : W64 (w : Int) ≠ W64 (if rt then 1 else 0) := by
      intro h; apply hb; cases rt <;> simp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;> word
    cases rt with
    | true =>
      simp only [↓reduceIte] at hb'
      try wp_auto
      simp only [hb', decide_false]
      try wp_auto
      ihave Hlb := Hcl $$ %w %Hwb.1 Hwf
      wp_apply hAppend out_ptr p P w (W8 47) (by omega) $$ [Hlb] as ⟨%P1, Hlb, %HP1⟩
      · iframe
      try wp_auto
      have H1 : P1.take (w + 1) = P.take w ++ [path.slash] ∧ w + 1 ≤ r ∧ dd ≤ w + 1 ∧
          P1.length = p.length := ⟨HP1.1, by omega, by omega, HP1.2⟩
      copy_loop P1 (w + 1)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hb'
      try wp_auto
      simp only [hb', decide_false]
      try wp_auto
      ihave Hlb := Hcl $$ %w %Hwb.1 Hwf
      wp_apply hAppend out_ptr p P w (W8 47) (by omega) $$ [Hlb] as ⟨%P1, Hlb, %HP1⟩
      · iframe
      try wp_auto
      have H1 : P1.take (w + 1) = P.take w ++ [path.slash] ∧ w + 1 ≤ r ∧ dd ≤ w + 1 ∧
          P1.length = p.length := ⟨HP1.1, by omega, by omega, HP1.2⟩
      copy_loop P1 (w + 1)))

set_option maxHeartbeats 8000000 in
theorem path.Clean.wp_proof
    (hIndex : path.lazybuf.index.spec (GF := GF) (hG := hG))
    (hAppend : path.lazybuf.append.spec (GF := GF) (hG := hG))
    (hString : path.lazybuf.string.spec (GF := GF) (hG := hG)) :
    path.Clean.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; ipureintro; rfl
  have Hpne : p ≠ [] := Hif
  obtain ⟨b0, Hb0⟩ : ∃ b, p[0]? = some b := ⟨_, List.getElem?_eq_getElem (by
    cases p with | nil => exact absurd rfl Hpne | cons _ _ => simp)⟩
  simp only [show sint.nat (W64 0) = 0 by rfl, show (0 : Int) ≤ sint.Z (W64 0) by decide,
    ↓reduceIte, Hb0]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hpl
  try wp_auto
  have Hn1 : 1 ≤ p.length := by cases p with | nil => exact absurd rfl Hpne | cons _ _ => simp
  have Hg0 : p.getD 0 0 = b0 := by simp [List.getD, Hb0]
  -- the model's run, from the loop's start
  obtain ⟨rt, Hrt⟩ : ∃ rt, rt = decide (b0 = W8 47) := ⟨_, rfl⟩
  rw [← Hrt]
  obtain ⟨F, HF⟩ : ∃ F, F = path.cleanLoop p rt (if rt then 1 else 0)
      (if rt then [path.slash] else []) (if rt then 1 else 0) := ⟨_, rfl⟩
  have HFm : path.cleanModel p = if F = [] then go!"." else F := by
    simp only [path.cleanModel, Hpne, ↓reduceIte, Hg0, HF, Hrt]
  icases typedPointsto_split _ _ _ $$ out with out
  simp only [TypedPointsto.typedPointstoDef, named]
  icases out with ⟨s, buf, w, -⟩
  ihave Hlb : path.lbOwn out_ptr p p 0 $$ [s buf w]
  · iunfold path.lbOwn
    iexists slice.nil
    iframe
    isplitr
    · ipureintro; omega
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_join iprop(∃ (r dd w : Nat) (P : List w8), "r" ∷ r_ptr ↦ W64 (r : Int) ∗
      "dotdot" ∷ dotdot_ptr ↦ W64 (dd : Int) ∗ "Hlb" ∷ path.lbOwn out_ptr p P w ∗
      "%Hinv" ∷ ⌜path.cleanInv p rt F r dd w P⌝) with [r dotdot Hlb]
  · iexists 0, 0, 0, p
    iframe
    ipureintro
    refine ⟨Nat.le_refl _, Nat.zero_le _, Nat.le_refl _, rfl, Or.inl rfl, by simp, ?_⟩
    rw [HF]; try simp
  · wp_apply hAppend out_ptr p p 0 (W8 47) (by omega) $$ [Hlb] as ⟨%P', Hlb, %HP'⟩
    · iframe
    try wp_auto
    wp_join_done
    iexists 1, 1, 1, P'
    simp only [show ((1 : Nat) : Int) = 1 by rfl]
    iframe
    ipureintro
    refine ⟨Nat.le_refl _, by omega, Nat.le_refl _, HP'.2, Or.inl rfl, fun _ => Nat.le_refl _, ?_⟩
    rw [HF, show P'.take 1 = [path.slash] by rw [HP'.1]; rfl]; simp
  iintro HI
  try wp_auto
  wp_for HI
  obtain ⟨Hwr, Hrn, Hdw, HPl, Hdisj, Hrt1, Hrun⟩ := Hinv
  have Hplen : p.length < 2 ^ 63 := Hpl
  have hr63 : r < 2 ^ 63 := by omega
  have hzr : sint.Z (W64 (r : Int)) = r := by word
  have hzn : sint.Z (W64 (p.length : Int)) = p.length := by word
  by_cases hr : r < p.length
  · have hc : sint.Z (W64 (r : Int)) < sint.Z (W64 (p.length : Int)) := by omega
    simp only [hc, decide_true]
    rw [if_pos (by simp)]
    try wp_auto
    have hz0 : 0 ≤ sint.Z (W64 (r : Int)) := by omega
    have hn0 : sint.nat (W64 (r : Int)) = r := by word
    obtain ⟨c, hpc⟩ : ∃ c, p[r]? = some c := ⟨_, List.getElem?_eq_getElem hr⟩
    have hgc : p.getD r 0 = c := by simp [List.getD, hpc]
    simp only [hz0, ↓reduceIte, hn0, hpc]
    try wp_auto
    have Hrun' := path.cleanLoop_step p rt r (P.take w) dd hr
    rw [Hrun] at Hrun'
    by_cases h1 : c = W8 47
    · -- `/`: an empty element
      subst h1
      try wp_auto
      have Hst : path.cleanStep p rt r (P.take w) dd = (r + 1, P.take w, dd) := by
        rw [path.cleanStep, if_pos hgc]
      rw [Hst] at Hrun'
      wp_for_post
      iframe
      iexists r + 1, dd, w, P
      rw [show W64 ((r + 1 : Nat) : Int) = W64 (r : Int) + W64 1 by word]
      iframe
      ipureintro
      exact ⟨by omega, by omega, Hdw, HPl, Or.inr (Or.inl (by omega)), Hrt1, Hrun'.symm⟩
    · simp only [decide_eq_false h1]
      try wp_auto
      simp only [hz0, ↓reduceIte, hn0, hpc]
      try wp_auto
      by_cases h2 : c = W8 46
      · subst h2
        try wp_auto
        have hn1 : ¬ p.getD r 0 = path.slash := by rw [hgc]; decide
        by_cases hr1 : r + 1 = p.length
        · -- `.` at the end
          have he : W64 (r : Int) + W64 1 = W64 (p.length : Int) := by rw [← hr1]; word
          simp only [he, _root_.decide_true]
          try wp_auto
          have Hst2 : path.cleanStep p rt r (P.take w) dd = (r + 1, P.take w, dd) := by
            rw [path.cleanStep, if_neg hn1, if_pos ⟨hgc, Or.inl hr1⟩]
          case_dot
        · have he : W64 (r : Int) + W64 1 ≠ W64 (p.length : Int) := by intro h; apply hr1; word
          simp only [he, _root_.decide_false]
          try wp_auto
          have hr1' : r + 1 < p.length := by omega
          have hz1 : 0 ≤ sint.Z (W64 (r : Int) + W64 1) := by word
          have hn1' : sint.nat (W64 (r : Int) + W64 1) = r + 1 := by word
          obtain ⟨c1, hpc1⟩ : ∃ c, p[r + 1]? = some c := ⟨_, List.getElem?_eq_getElem hr1'⟩
          have hgc1 : p.getD (r + 1) 0 = c1 := by simp [List.getD, hpc1]
          simp only [hz1, ↓reduceIte, hn1', hpc1]
          try wp_auto
          by_cases hs1 : c1 = W8 47
          · -- `./`
            rw [decide_eq_true hs1]
            try wp_auto
            have Hst2 : path.cleanStep p rt r (P.take w) dd = (r + 1, P.take w, dd) := by
              rw [path.cleanStep, if_neg hn1, if_pos ⟨hgc, Or.inr (hgc1.trans hs1)⟩]
            case_dot
          · rw [decide_eq_false hs1]
            try wp_auto
            have hn2 : ¬ (p.getD r 0 = path.dot ∧ (r + 1 = p.length ∨ p.getD (r + 1) 0 = path.slash)) := by
              rintro ⟨-, h | h⟩
              · exact hr1 h
              · exact hs1 (hgc1 ▸ h)
            simp only [hz0, ↓reduceIte, hn0, hpc]
            try wp_auto
            simp only [hz1, ↓reduceIte, hn1', hpc1]
            try wp_auto
            by_cases hd1 : c1 = W8 46
            · rw [decide_eq_true hd1]
              try wp_auto
              by_cases hr2 : r + 2 = p.length
              · -- `..` at the end
                have he2 : W64 (r : Int) + W64 2 = W64 (p.length : Int) := by rw [← hr2]; word
                simp only [he2, _root_.decide_true]
                try wp_auto
                have H3 : p.getD r 0 = path.dot ∧ p.getD (r + 1) 0 = path.dot ∧
                    (r + 2 = p.length ∨ p.getD (r + 2) 0 = path.slash) :=
                  ⟨hgc, hgc1.trans hd1, Or.inl hr2⟩
                rw [path.cleanStep, if_neg hn1, if_neg hn2, if_pos H3] at Hrun'
                case_dotdot
              · have he2 : W64 (r : Int) + W64 2 ≠ W64 (p.length : Int) := by
                  intro h; apply hr2; word
                simp only [he2, _root_.decide_false]
                try wp_auto
                have hr2' : r + 2 < p.length := by omega
                have hz2 : 0 ≤ sint.Z (W64 (r : Int) + W64 2) := by word
                have hnn2 : sint.nat (W64 (r : Int) + W64 2) = r + 2 := by word
                obtain ⟨c2, hpc2⟩ : ∃ c, p[r + 2]? = some c := ⟨_, List.getElem?_eq_getElem hr2'⟩
                have hgc2 : p.getD (r + 2) 0 = c2 := by simp [List.getD, hpc2]
                simp only [hz2, ↓reduceIte, hnn2, hpc2]
                try wp_auto
                by_cases hs2 : c2 = W8 47
                · -- `../`
                  rw [decide_eq_true hs2]
                  try wp_auto
                  have H3 : p.getD r 0 = path.dot ∧ p.getD (r + 1) 0 = path.dot ∧
                      (r + 2 = p.length ∨ p.getD (r + 2) 0 = path.slash) :=
                    ⟨hgc, hgc1.trans hd1, Or.inr (hgc2.trans hs2)⟩
                  rw [path.cleanStep, if_neg hn1, if_neg hn2, if_pos H3] at Hrun'
                  case_dotdot
                · -- `..x`: a real element
                  rw [decide_eq_false hs2]
                  try wp_auto
                  have hn3 : ¬ (p.getD r 0 = path.dot ∧ p.getD (r + 1) 0 = path.dot ∧
                      (r + 2 = p.length ∨ p.getD (r + 2) 0 = path.slash)) := by
                    rintro ⟨-, -, h | h⟩
                    · exact hr2 h
                    · exact hs2 (hgc2 ▸ h)
                  have Hst : path.cleanStep p rt r (P.take w) dd =
                      ((path.copyElem p r (if (rt = true ∧ (P.take w).length ≠ 1) ∨
                        ((!rt) = true ∧ (P.take w).length ≠ 0) then P.take w ++ [path.slash]
                          else P.take w)).1,
                       (path.copyElem p r (if (rt = true ∧ (P.take w).length ≠ 1) ∨
                        ((!rt) = true ∧ (P.take w).length ≠ 0) then P.take w ++ [path.slash]
                          else P.take w)).2,
                       dd) := by
                    rw [path.cleanStep, if_neg hn1, if_neg hn2, if_neg hn3]
                  rw [Hst] at Hrun'
                  case_default
            · -- `.x`: a real element
              rw [decide_eq_false hd1]
              try wp_auto
              have hn3 : ¬ (p.getD r 0 = path.dot ∧ p.getD (r + 1) 0 = path.dot ∧
                  (r + 2 = p.length ∨ p.getD (r + 2) 0 = path.slash)) := by
                rintro ⟨-, h, -⟩; exact hd1 (hgc1 ▸ h)
              have Hst : path.cleanStep p rt r (P.take w) dd =
                ((path.copyElem p r (if (rt = true ∧ (P.take w).length ≠ 1) ∨
                  ((!rt) = true ∧ (P.take w).length ≠ 0) then P.take w ++ [path.slash] else P.take w)).1,
                 (path.copyElem p r (if (rt = true ∧ (P.take w).length ≠ 1) ∨
                  ((!rt) = true ∧ (P.take w).length ≠ 0) then P.take w ++ [path.slash] else P.take w)).2,
                 dd) := by
                rw [path.cleanStep, if_neg hn1, if_neg hn2, if_neg hn3]
              rw [Hst] at Hrun'
              case_default
      · simp only [decide_eq_false h2]
        try wp_auto
        simp only [hz0, ↓reduceIte, hn0, hpc]
        try wp_auto
        simp only [h2, decide_false]
        try wp_auto
        -- a real element
        have Hst : path.cleanStep p rt r (P.take w) dd =
            ((path.copyElem p r (if (rt = true ∧ (P.take w).length ≠ 1) ∨
              ((!rt) = true ∧ (P.take w).length ≠ 0) then P.take w ++ [path.slash] else P.take w)).1,
             (path.copyElem p r (if (rt = true ∧ (P.take w).length ≠ 1) ∨
              ((!rt) = true ∧ (P.take w).length ≠ 0) then P.take w ++ [path.slash] else P.take w)).2,
             dd) := by
          rw [path.cleanStep, if_neg (by rw [hgc]; exact h1), if_neg (by rw [hgc]; intro h; exact h2 h.1),
            if_neg (by rw [hgc]; intro h; exact h2 h.1)]
        rw [Hst] at Hrun'
        case_default
  · -- the loop's end: `"."` if the output is empty, else the output
    have hc : ¬ sint.Z (W64 (r : Int)) < sint.Z (W64 (p.length : Int)) := by omega
    rw [if_neg (by simp only [decide_eq_true_eq]; exact hc)]
    rw [if_neg (by simp only [decide_eq_true_eq]; exact hc)]
    try wp_auto
    rw [path.cleanLoop_stop _ _ _ _ _ hr] at Hrun
    ihave ⟨Hwf, %Hwb, Hcl⟩ := path.lbOwn_w $$ Hlb
    try wp_auto
    by_cases hw0 : w = 0
    · subst hw0
      try wp_auto
      iapply HΦ
      ipureintro
      rw [HFm, ← Hrun]; simp
    · have hwz : W64 (w : Int) ≠ W64 0 := by intro h; apply hw0; word
      simp only [decide_eq_false hwz]
      try wp_auto
      ihave Hlb := Hcl $$ %w %Hwb.1 Hwf
      wp_apply hString out_ptr p P w Hwb.2.2 $$ [Hlb]
      · iframe
      try wp_auto
      iapply HΦ
      ipureintro
      have hne : P.take w ≠ [] := by
        rw [Ne, List.take_eq_nil_iff]
        rintro (h | h)
        · exact hw0 h
        · subst h; simp at HPl; omega
      rw [HFm, ← Hrun]; simp [hne]

end proof

end EtcdGrove
end Perennial
