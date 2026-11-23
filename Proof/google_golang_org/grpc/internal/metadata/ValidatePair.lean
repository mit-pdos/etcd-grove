/-
The proof of `Spec/google_golang_org/grpc/internal/metadata/ValidatePair.lean`: `ValidateKey`, the
`-bin` suffix (Perennial's `strings.HasSuffix`), then the range over the values (its invariant: the
values before the index are printable); the error is `fmt.Errorf`'s.
-/
module

public import Spec.google_golang_org.grpc.internal.metadata.ValidatePair
public import Spec.google_golang_org.grpc.internal.metadata.ValidateKey
public import Spec.google_golang_org.grpc.internal.metadata.hasNotPrintable
public import Perennial.Spec.strings.HasSuffix

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.metadata.Assumptions]

theorem imetadata.ValidatePair.wp_proof
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_ValidateKey : imetadata.ValidateKey.spec (GF := GF) (hG := hG))
    (wp_hasNotPrintable : imetadata.hasNotPrintable.spec (GF := GF) (hG := hG))
    (wp_HasSuffix : _root_.Perennial.strings.HasSuffix.spec (GF := GF) (hG := hG)) :
    imetadata.ValidatePair.spec (GF := GF) (hG := hG) := by
  intro key vals_sl vs dq
  wp_start as Hsl
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_ValidateKey key) $$ [Hpkg] as %e ⟨%He, #HeOk⟩
  rcases e with ei | _
  · -- the key is refused
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · ipureintro
      simp only [reduceCtorEq, false_iff]
      exact fun h => absurd (He.mpr h.1) (by simp)
    · iexact HeOk
  have Hk : grpcHdr.keyOk key := He.mp rfl
  wp_auto
  wp_apply (wp_HasSuffix key go!"-bin")
  wp_if_destruct
  · iapply HΦ
    iframe
    isplitr
    · ipureintro
      simp only [true_iff]
      exact ⟨Hk, Or.inl Hif⟩
    · iapply fmtErrorOkOrNil_nil
  have Hns : ¬ go!"-bin" <:+ key := Hif
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (n : w64) (v : GoString),
      "i" ∷ i_ptr ↦ n ∗ "val" ∷ val_ptr ↦ v ∗ "res" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
      "key" ∷ key_ptr ↦ key ∗ "Hsl" ∷ vals_sl ↦*{dq} vs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ vs.length ∧
        ∀ j (h : j < sint.nat n), ∀ hj : j < vs.length, ∀ b ∈ vs[j], grpcHdr.printable b⌝)
      $$ [i val «$res0» key Hsl]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by rw [show sint.nat (W64 0) = 0 by decide]; omega,
      fun j h => absurd h (by rw [show sint.nat (W64 0) = 0 by decide]; omega)⟩
  wp_for IH
  cleanup_bool_decide
  obtain ⟨Hn0, HnL, Hpre⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by clear Hpre; word
    obtain ⟨v1, Hv1⟩ : ∃ v1, vs[sint.nat n]? = some v1 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vals_sl.len := ⟨Hn0, by clear Hpre; word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index vals_sl (sint.Z n) _ dq v1 Hn0 $$ [$Hsl] as Hsl
    · ipureintro; rw [show (sint.Z n).toNat = sint.nat n by rfl]; exact Hv1
    wp_apply (wp_hasNotPrintable v1)
    by_cases hp : ∀ b ∈ v1, grpcHdr.printable b
    · rw [decide_eq_true hp]
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, v1
      simp only [named]
      iframe
      ipureintro
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by clear Hpre; word
      have hn2 : 0 ≤ sint.Z (n + W64 1) := by clear Hpre; word
      refine ⟨hn2, by rw [hn1]; exact Hlt, fun j hj hjl => ?_⟩
      rw [hn1] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Hpre j h hjl
      · have hj2 : vs[j]? = some v1 := by rw [h]; exact Hv1
        rw [(List.getElem?_eq_some_iff.mp hj2).2]; exact hp
    · rw [decide_eq_false hp]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl', -⟩
      wp_apply (wp_Errorf _ _ _ (DFrac.own 1)) $$ [Hsl'] as %ei ⟨-, #HiS, %Hty, -⟩
      · iframe
        iapply (_root_.Perennial.fmt.argsOk_of_argsWf
          (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))
      wp_for_post
      iapply HΦ
      iframe
      isplitr
      · ipureintro
        simp only [reduceCtorEq, false_iff]
        rintro ⟨-, hs | hall⟩
        · exact Hns hs
        · exact hp (hall v1 (List.mem_of_getElem? Hv1))
      · iapply fmtErrorOkOrNil_of
        iapply fmtErrorOk_of_errorf ei Hty $$ HiS
  · -- the range is done: every value is printable
    have hn : vs.length ≤ sint.nat n := by clear Hpre; word
    iapply HΦ
    iframe
    isplitr
    · ipureintro
      simp only [true_iff]
      refine ⟨Hk, Or.inr fun x hx => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact Hpre j (Nat.lt_of_lt_of_le hj hn) hj
    · iapply fmtErrorOkOrNil_nil

end proof

end EtcdGrove
end Perennial
