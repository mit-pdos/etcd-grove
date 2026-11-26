/-
The proofs of `serve`'s helpers (`ServeDefs.lean`): `digit`, `nodeConfig` (over `digit.spec`),
`host` (the loop keeps `hostB s = hostAux s (i + 1)`), `itoa` (the loop keeps
`itoaDigits n₀ = itoaDigits n ++ b`; `mvccfull`'s `itoa` the template).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServeDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem digit.wp_proof : digit.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (W64 48 + n % W64 10))]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none
    (ElementExpression go.byte #(W8 (uint.Z (W64 48 + n % W64 10))))] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Htmp, -⟩
  wp_apply wp_bytes_to_string $$ [$Htmp] as -
  iapply HΦ; itrivial

theorem nodeConfig.wp_proof (wp_digit : digit.spec (GF := GF) (hG := hG)) :
    nodeConfig.spec (GF := GF) (hG := hG) := by
  intro id port
  wp_start
  wp_auto
  wp_apply wp_digit id
  iapply HΦ
  iexists _
  iframe
  ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩

theorem host.wp_proof : host.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜-1 ≤ sint.Z i ∧ sint.Z i < s.length ∧
        hostB s = hostAux s (sint.Z i + 1).toNat⌝ : IProp GF) $$ [i]
  · iexists _
    iframe
    ipureintro
    have h : sint.Z (W64 (s.length : Int) - W64 1) = s.length - 1 := by word
    rw [h]
    refine ⟨by omega, by omega, ?_⟩
    rw [show ((s.length : Int) - 1 + 1).toNat = s.length by omega]
    rfl
  wp_for HI
  by_cases hge : sint.Z (W64 0) ≤ sint.Z i
  · rw [decide_eq_true hge]; simp only [↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z i := by simpa using hge
    have hn : sint.nat i < s.length := by
      have : sint.nat i = (sint.Z i).toNat := rfl
      omega
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hn⟩
    simp only [h0, ↓reduceIte, hb]
    wp_auto
    by_cases hc : b = W8 58
    · subst hc
      simp only [decide_true]
      wp_auto
      have hsl : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z i ∧ sint.Z i ≤ s.length :=
        ⟨by decide, by simpa using h0, by omega⟩
      simp only [hsl, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_for_post
      have hh : hostB s = (s.drop 0).take (sint.nat i - 0) := by
        rw [Hi.2.2, show (sint.Z i + 1).toNat = sint.nat i + 1 by
          have : sint.nat i = (sint.Z i).toNat := rfl
          omega]
        simp only [hostAux, hb, ↓reduceIte, List.drop_zero, Nat.sub_zero]
      rw [← hh]
      iapply HΦ; itrivial
    · simp only [decide_eq_false hc]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hd : sint.Z (i - W64 1) = sint.Z i - 1 := by word
      rw [hd]
      refine ⟨by omega, by omega, ?_⟩
      rw [Hi.2.2, show (sint.Z i + 1).toNat = sint.nat i + 1 by
          have : sint.nat i = (sint.Z i).toNat := rfl
          omega, show (sint.Z i - 1 + 1).toNat = sint.nat i by
          have : sint.nat i = (sint.Z i).toNat := rfl
          omega]
      simp only [hostAux, hb, Option.some.injEq, hc, ↓reduceIte]
  · rw [decide_eq_false hge]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : (sint.Z i + 1).toNat = 0 := by
      have : ¬ (0 ≤ sint.Z i) := by simpa using hge
      omega
    rw [Hi.2.2, hi, show hostAux s 0 = s from rfl]
    iapply HΦ; itrivial

theorem itoa.wp_proof : itoa.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 48]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #(W8 48))] = 1
      from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sp ⟨Hs, -⟩
    wp_auto
    iapply HΦ
    rw [show itoaB (uint.nat (W64 0)) = [W8 48] from rfl]
    iexact Hs
  · (try wp_auto)
    have hn0 : uint.nat n ≠ 0 := by intro h; apply Hif; word
    ihave HI : (∃ (m : w64) (b : GoSlice) (bs : List w8),
        "n" ∷ n_ptr ↦ m ∗ "b" ∷ b_ptr ↦ b ∗ "Hb" ∷ b ↦* bs ∗
        "%Hm" ∷ ⌜itoaDigits (uint.nat n) = itoaDigits (uint.nat m) ++ bs⌝ :
        IProp GF) $$ [n b]
    · iexists n, slice.nil, []
      iframe
      isplitl
      · iapply ownSlice_nil
      ipureintro; simp
    wp_for HI
    by_cases Hlt : uint.Z (W64 0) < uint.Z m
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, Hcap⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hosl $Hcap $Hb] as %b' ⟨Hb', -, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, b', _
      iframe
      ipureintro
      rw [Hm, itoaDigits_pos (uint.nat m) (by word), List.append_assoc]
      have hq : uint.nat (m / W64 10) = uint.nat m / 10 := by word
      have hr : uint.Z (W64 48 + m % W64 10) = ((48 + uint.nat m % 10 : Nat) : Int) := by word
      rw [hq, hr]
    · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hm0 : uint.nat m = 0 := by word
      rw [hm0, itoaDigits_zero, List.nil_append] at Hm
      (try wp_auto)
      iapply HΦ
      unfold itoaB
      rw [ite_eq_right_iff.2 (fun h => absurd h hn0), Hm]
      iexact Hb

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
