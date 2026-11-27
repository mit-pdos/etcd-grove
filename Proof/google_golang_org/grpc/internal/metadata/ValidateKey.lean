/-
The proof of `Spec/google_golang_org/grpc/internal/metadata/ValidateKey.lean`: the empty key, the
pseudo-header, then the byte loop (its invariant: the bytes before the index are `keyByteOk`); the
errors are `fmt.Errorf`'s.
-/
module

public import Spec.google_golang_org.grpc.internal.metadata.ValidateKey

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
-- the byte test's case split tries each comparison's `by_cases` with one `simp` set for both cases
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

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

theorem imetadata.ValidateKey.wp_proof
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    imetadata.ValidateKey.spec (GF := GF) (hG := hG) := by
  intro key
  wp_start as #Hpkg
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · -- the empty key
    ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
    wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [Hnil] as %ei ⟨-, #HiS, %Hty, -⟩
    · iframe
      isplitr
      · iexact Hnil
      · iapply (_root_.Perennial.fmt.argsOk_of_argsWf _root_.Perennial.fmt.ArgsWf.nil)
    iapply HΦ
    isplitr
    · ipureintro; simp [grpcHdr.keyOk]
    · iapply fmtErrorOkOrNil_of
      iapply fmtErrorOk_of_errorf ei Hty $$ HiS
  obtain ⟨c, t, rfl⟩ : ∃ c t, key = c :: t := by
    cases key with
    | nil => exact absurd rfl Hif
    | cons c t => exact ⟨c, t, rfl⟩
  simp only [List.getElem?_cons_zero]
  wp_auto
  wp_if_destruct
  · -- a pseudo-header
    iapply HΦ
    isplitr
    · ipureintro; simp [grpcHdr.keyOk]
    · iapply fmtErrorOkOrNil_nil
  have Hc : c ≠ W8 58 := Hif
  ihave IH : iprop(∃ (n : w64),
      "i" ∷ i_ptr ↦ n ∗ "res" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
      "key" ∷ key_ptr ↦ (c :: t) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ (c :: t).length ∧
        ∀ j (h : j < sint.nat n), ∀ hj : j < (c :: t).length, grpcHdr.keyByteOk (c :: t)[j]⌝)
      $$ [i «$res0» key]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by rw [show sint.nat (W64 0) = 0 by decide]; omega, fun j h => absurd h (by rw [show sint.nat (W64 0) = 0 by decide]; omega)⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  cleanup_bool_decide
  obtain ⟨Hn0, HnL, Hpre⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < (c :: t).length := by clear Hpre; word
    obtain ⟨b, Hb⟩ : ∃ b, (c :: t)[sint.nat n]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left Hn0, Hb]
    wp_auto
    have Hok : grpcHdr.keyByteOk b → ∀ j (hj : j < (c :: t).length), j = sint.nat n →
        grpcHdr.keyByteOk (c :: t)[j] := fun h j hj e => by
      subst e; rw [(List.getElem?_eq_some_iff.mp Hb).2]; exact h
    have Hbad : ¬ grpcHdr.keyByteOk b → ¬ grpcHdr.keyOk (c :: t) := fun hb ⟨_, h⟩ => by
      rcases h with h | h
      · exact Hc (by simpa using h)
      · exact hb (h b (List.mem_of_getElem? Hb))
    repeat' (first
      | wp_if_destruct
      | (by_cases hq : uint.Z (W8 48) ≤ uint.Z b <;>
          simp only [hq, decide_true, decide_false] <;> wp_auto)
      | (by_cases hq : b = W8 46 <;> simp only [hq, decide_true, decide_false] <;> wp_auto)
      | (by_cases hq : b = W8 45 <;> simp only [hq, decide_true, decide_false] <;> wp_auto)
      | (by_cases hq : b = W8 95 <;> simp only [hq, decide_true, decide_false] <;> wp_auto))
    all_goals first
      | (have hk := Hok (by clear Hpre Hok Hbad; rw [grpcHdr.keyByteOk_iff]; word)
         wp_for_post
         iframe
         iexists n + W64 1
         simp only [named]
         iframe
         ipureintro
         have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by clear Hpre Hok Hbad hk; word
         have hn2 : 0 ≤ sint.Z (n + W64 1) := by clear Hpre Hok Hbad hk; word
         refine ⟨hn2, by rw [hn1]; exact Hlt, fun j hj hjl => ?_⟩
         rw [hn1] at hj
         rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
         · exact Hpre j h hjl
         · exact hk j hjl h)
      | (have hk := Hbad (by clear Hpre Hok Hbad; rw [grpcHdr.keyByteOk_iff]; word)
         wp_apply wp_slice_literal
         isplitr
         · ipureintro; rfl
         iintro %sl ⟨Hsl, -⟩
         wp_apply (wp_Errorf _ _ _ (DFrac.own 1)) $$ [Hsl] as %ei ⟨-, #HiS, %Hty, -⟩
         · iframe
           iapply (_root_.Perennial.fmt.argsOk_of_argsWf
             (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))
         wp_for_post
         iapply HΦ
         isplitr
         · ipureintro; simp only [reduceCtorEq, false_iff]; exact hk
         · iapply fmtErrorOkOrNil_of
           iapply fmtErrorOk_of_errorf ei Hty $$ HiS)
  · -- the loop is done: every byte is `keyByteOk`
    have hn : (c :: t).length ≤ sint.nat n := by clear Hpre; word
    iapply HΦ
    isplitr
    · ipureintro
      simp only [true_iff]
      refine ⟨by simp, Or.inr fun x hx => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact Hpre j (Nat.lt_of_lt_of_le hj hn) hj
    · iapply fmtErrorOkOrNil_nil

end proof

end EtcdGrove
end Perennial
