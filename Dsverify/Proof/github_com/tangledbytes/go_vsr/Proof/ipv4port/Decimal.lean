/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/ipv4port/Decimal.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
`decimal(n)` (`n ≥ 0`): `n` in decimal (`decStr`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The decimal digits of `n` with fuel `f` (none for `0`). -/
def ipv4port.digitsF : Nat → Nat → List w8
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else ipv4port.digitsF f (n / 10) ++ [W8 (48 + (n % 10 : Nat))]

/-- The decimal digits of `n` (none for `0`). -/
def ipv4port.digits (n : Nat) : List w8 := ipv4port.digitsF n n

/-- `n` in decimal, as `fmt`'s `%d`. -/
def ipv4port.decStr (n : Nat) : List w8 := if n = 0 then [W8 48] else ipv4port.digits n

theorem ipv4port.digitsF_fuel (f : Nat) : ∀ (g n : Nat), n ≤ f → n ≤ g →
    ipv4port.digitsF f n = ipv4port.digitsF g n := by
  induction f with
  | zero =>
    intro g n hf hg
    have : n = 0 := by omega
    subst this
    cases g <;> simp [ipv4port.digitsF]
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero =>
      have : n = 0 := by omega
      subst this; simp [ipv4port.digitsF]
    | succ g =>
      simp only [ipv4port.digitsF]
      split
      · rfl
      · rw [ih g (n / 10) (by omega) (by omega)]

theorem ipv4port.digits_step (n : Nat) (h : n ≠ 0) :
    ipv4port.digits n = ipv4port.digits (n / 10) ++ [W8 (48 + (n % 10 : Nat))] := by
  unfold ipv4port.digits
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [ipv4port.digitsF, Nat.add_one_ne_zero, ↓reduceIte]
  rw [ipv4port.digitsF_fuel m ((m + 1) / 10) ((m + 1) / 10) (by omega) (Nat.le_refl _)]

theorem ipv4port.digits_zero : ipv4port.digits 0 = [] := by
  simp [ipv4port.digits, ipv4port.digitsF]

/-- The loop condition `if #(decide P) = #true` (whatever the decidability instance of the
`val` equality). -/
theorem ipv4port.ite_val_true {A : Type _} [GooseExts] [GoGlobalContext] (P : Prop) [Decidable P]
    [i : Decidable ((#(decide P) : val) = #true)] (x y : A) :
    (if @decide _ i = true then x else y) = if P then x else y := by
  by_cases h : P
  · simp [h]
  · simp only [h, decide_false, if_false]
    rw [if_neg]
    simp only [decide_eq_true_eq]
    intro h'
    exact absurd (GoGlobalContext.intoVal_inj_bool h') (by decide)

theorem ipv4port.ite_val_false {A : Type _} [GooseExts] [GoGlobalContext] (P : Prop) [Decidable P]
    [i : Decidable ((#(decide P) : val) = #false)] (x y : A) :
    (if @decide _ i = true then x else y) = if P then y else x := by
  by_cases h : P
  · simp only [h, decide_true, if_true]
    rw [if_neg]
    simp only [decide_eq_true_eq]
    intro h'
    exact absurd (GoGlobalContext.intoVal_inj_bool h') (by decide)
  · simp [h]

theorem ipv4port.sdiv10 (m : w64) (h : 0 ≤ sint.Z m) :
    0 ≤ sint.Z (BitVec.sdiv m (W64 10)) ∧ sint.nat (BitVec.sdiv m (W64 10)) = sint.nat m / 10 := by
  constructor <;> word

theorem ipv4port.srem10 (m : w64) (h : 0 ≤ sint.Z m) :
    W8 (sint.Z (W64 48 + BitVec.srem m (W64 10))) = W8 (48 + (sint.nat m % 10 : Nat)) := by
  have h1 : sint.Z (BitVec.srem m (W64 10)) = sint.Z m % 10 := by
    show (BitVec.srem m (W64 10)).toInt = _
    rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg h]
    rfl
  have h2 : sint.Z (W64 48 + BitVec.srem m (W64 10)) = 48 + ((sint.nat m % 10 : Nat) : Int) := by
    have : ((sint.nat m % 10 : Nat) : Int) = sint.Z m % 10 := by
      have : ((sint.nat m : Nat) : Int) = sint.Z m := by word
      omega
    rw [this]
    word
  rw [h2]

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

theorem ipv4port.wp_decimal (n : w64) (hn : 0 ≤ sint.Z n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port }}
      (App (Val (@! ipv4port.decimal)) (Val #n))
    {{ RET #(ipv4port.decStr (sint.nat n)); True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show ipv4port.decStr (sint.nat (W64 0)) = [48#8] from rfl]
    wp_end
  · have Hn0 : n ≠ W64 0 := Hif
    ihave HI : (∃ (m : w64) (sl : GoSlice) (bs : List w8),
        "n" ∷ n_ptr ↦ m ∗ "b" ∷ b_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* bs ∗
        "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ ipv4port.digits (sint.nat m) ++ bs = ipv4port.digits (sint.nat n)⌝ :
        IProp GF) $$ [n b]
    · iexists n, slice.nil, []
      iframe
      isplitl []; iapply ownSlice_nil
      isplitl []; iapply ownSliceCap_nil
      ipureintro; simp [hn]
    wp_for HI
    wp_if_destruct
    · wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (sint.Z (W64 48 + BitVec.srem m (W64 10)))]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hsl1, Hsl1_cap⟩
      wp_auto
      wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ sl bs (DFrac.own 1) $$ [Hsl1 Hsl1_cap Hsl]
        with %s' ⟨Hs', Hs'_cap, Hsl⟩
      · iframe
      wp_for_post
      iframe
      obtain ⟨h1, h2⟩ := ipv4port.sdiv10 m Hm.1
      iexists BitVec.sdiv m (W64 10), s', _
      iframe
      ipureintro
      refine ⟨h1, ?_⟩
      rw [h2, ipv4port.srem10 m Hm.1, ← Hm.2, ipv4port.digits_step (sint.nat m) (by word)]
      simp
    · have hm0 : sint.nat m = 0 := by word
      rw [hm0, ipv4port.digits_zero, List.nil_append] at Hm
      wp_apply wp_bytes_to_string sl bs (DFrac.own 1) $$ [$Hsl] with Hsl
      have hd : bs = ipv4port.decStr (sint.nat n) := by
        rw [Hm.2]; unfold ipv4port.decStr; rw [if_neg]; intro h; apply Hn0; word
      rw [hd]
      iapply HΦ
      try itrivial

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
