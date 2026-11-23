/-
The proof of `Spec/google_golang_org/grpc/internal/metadata/hasNotPrintable.lean`: the byte loop, its
invariant that the bytes before the index are printable.
-/
module

public import Spec.google_golang_org.grpc.internal.metadata.hasNotPrintable

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

theorem imetadata.hasNotPrintable.wp_proof :
    imetadata.hasNotPrintable.spec (GF := GF) (hG := hG) := by
  intro msg
  wp_start as -
  wp_auto
  ihave IH : iprop(∃ (n : w64),
      "i" ∷ i_ptr ↦ n ∗ "res" ∷ «$res0_ptr» ↦ false ∗ "msg" ∷ msg_ptr ↦ msg ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ msg.length ∧
        ∀ j (h : j < sint.nat n), ∀ hj : j < msg.length, grpcHdr.printable msg[j]⌝) $$ [i «$res0» msg]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by simp, fun j h => absurd h (by simp)⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  cleanup_bool_decide
  obtain ⟨Hn0, HnL, Hpre⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < msg.length := by clear Hpre; word
    obtain ⟨b, Hb⟩ : ∃ b, msg[sint.nat n]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left Hn0, Hb]
    wp_auto
    have Hbad : ¬ grpcHdr.printable b → ¬ ∀ c ∈ msg, grpcHdr.printable c := fun hb hall =>
      hb (hall b (List.mem_of_getElem? Hb))
    wp_if_destruct
    · -- `b < 0x20`
      wp_for_post
      have hb : ¬ grpcHdr.printable b := by
        clear Hpre Hbad Hb
        unfold grpcHdr.printable; simp only [BitVec.le_def]; intro ⟨h, _⟩; word
      rw [decide_eq_true (Hbad hb)]
      iapply HΦ; itrivial
    · rw [ite_eq_left Hn0, Hb]
      wp_auto
      wp_if_destruct
      · -- `b > 0x7E`
        wp_for_post
        have hb : ¬ grpcHdr.printable b := by
          clear Hpre Hbad Hb
          unfold grpcHdr.printable; simp only [BitVec.le_def]; intro ⟨_, h⟩; word
        rw [decide_eq_true (Hbad hb)]
        iapply HΦ; itrivial
      · wp_for_post
        iframe
        iexists n + W64 1
        simp only [named]
        iframe
        ipureintro
        have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by clear Hpre Hbad Hb; word
        have hn2 : 0 ≤ sint.Z (n + W64 1) := by clear Hpre Hbad Hb; word
        have hp : grpcHdr.printable b := by
          clear Hpre Hbad Hb
          unfold grpcHdr.printable; simp only [BitVec.le_def]; constructor <;> word
        refine ⟨hn2, by rw [hn1]; exact Hlt, fun j hj hjl => ?_⟩
        rw [hn1] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Hpre j h hjl
        · have hj2 : msg[j]? = some b := by rw [h]; exact Hb
          rw [(List.getElem?_eq_some_iff.mp hj2).2]; exact hp
  · have hn : msg.length ≤ sint.nat n := by clear Hpre; word
    have Hall : ∀ c ∈ msg, grpcHdr.printable c := by
      intro c hc
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      exact Hpre j (Nat.lt_of_lt_of_le hj hn) hj
    rw [decide_eq_false (fun h => h Hall)]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
