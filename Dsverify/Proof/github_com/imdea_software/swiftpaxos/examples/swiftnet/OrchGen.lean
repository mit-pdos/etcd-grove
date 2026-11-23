/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchGen.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The orchestrator's `Gen(c, j)` and `Start(c)` (`kit.go`), with `digits(n)` and `mix(c, r)`: the
inputs meet `kit.pre` (8-byte keys `"key00000"`, `"key00001"`: `"key0000"` and one digit of
`mix(c, j/2) mod NKeys`; put values `"v<c>.<j>"`, non-empty and short), and the start delay is a
number.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]

/-- `digits(n)`: a decimal string of at most `k` characters when `n < 10^k`; one digit
character for `n < 10`. -/
abbrev digits.spec : Prop :=
  ∀ (n : w64) (k : Nat), uint.nat n < 10 ^ k → 1 ≤ k →
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
    (App (Val (@! examples.swiftnet.digits)) (Val #n))
  {{ (s : GoString), RET #s; ⌜s ≠ [] ∧ s.length ≤ k ∧
      (uint.nat n < 10 → s = [W8 (48 + uint.Z n)])⌝ }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

theorem digits.wp_proof : digits.spec := by
  intro n
  induction h : uint.nat n using Nat.strongRecOn generalizing n with
  | _ m IH =>
  intro k hk hk1
  wp_start
  wp_auto
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (W64 48 + n))]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z (W64 48 + n))))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %c_sl ⟨Hc_sl, -⟩
    wp_apply wp_bytes_to_string $$ Hc_sl as -
    iapply HΦ
    ipureintro
    have hn : uint.Z n < 10 := by word
    refine ⟨by simp, by simp; omega, fun _ => ?_⟩
    congr 1
    word
  · have hn10 : 10 ≤ uint.nat n := by word
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · simp at hk; omega
      · omega
    wp_apply IH (uint.nat (n / W64 10)) (by word) (n / W64 10) rfl (k - 1) ?_ (by omega)
      as %s1 %Hs1
    · rw [show uint.nat (n / W64 10) = uint.nat n / 10 by word]
      have h10 : 10 ^ k = 10 ^ (k - 1) * 10 := by
        rw [← Nat.pow_succ]; congr 1; omega
      rw [h] at *
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← h10]; exact hk)
    wp_apply IH (uint.nat (n % W64 10)) (by word) (n % W64 10) rfl 1 (by word) (Nat.le_refl _)
      as %s2 %Hs2
    iapply HΦ
    ipureintro
    have hs2 : s2.length = 1 := by
      rw [Hs2.2.2 (by word)]; rfl
    refine ⟨by simp [Hs1.1], ?_, fun h' => by omega⟩
    simp only [List.length_append, hs2]
    have := Hs1.2.1
    omega

end proofs

end orch

namespace orch

section gen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

theorem w64_lt_pow20 (n : w64) : uint.nat n < 10 ^ 20 := by
  have := n.isLt
  simp only [uint.nat, uint.Z] at *
  omega

/-- `mix(c, r)`: some number (a fixed hash; only its value modulo `NKeys` is used). -/
theorem mix.wp_proof (c r : w64) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
      (App (App (Val (@! examples.swiftnet.mix)) (Val #c)) (Val #r))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  iapply HΦ $$ %_ %trivial

theorem Gen.wp_proof (wp_digits : digits.spec) (c j : w64) :
    {{ isPkgInit (PROP := IProp netDistGF) kit.pkg }}
      (App (App (Val (@! kit.genF)) (Val #c)) (Val #j))
    {{ (i : (kv GoString GoString).Input), RET #(kit.encI i); ⌜kit.pre i⌝ }} := by
  dsimp only [kit]
  wp_start
  wp_auto
  wp_apply mix.wp_proof c (j / W64 2) as %x -
  wp_apply wp_digits (x % W64 2) 1 (by word) (Nat.le_refl _) as %kd %Hkd
  have hk : (go!"key0000" ++ kd).length = 8 := by
    rw [Hkd.2.2 (by word)]; rfl
  wp_if_destruct
  · wp_apply wp_digits c 20 (w64_lt_pow20 c) (by omega) as %d1 %Hd1
    wp_apply wp_digits j 20 (w64_lt_pow20 j) (by omega) as %d2 %Hd2
    ihave H := HΦ $$ %(KvInput.put (go!"key0000" ++ kd) (go!"v" ++ d1 ++ go!"." ++ d2))
    simp only [encKvIn, kvInV]
    iapply H
    ipureintro
    refine ⟨hk, by simp, ?_⟩
    simp only [List.length_append]
    have := Hd1.2.1
    have := Hd2.2.1
    simp
    omega
  · ihave H := HΦ $$ %(KvInput.get (go!"key0000" ++ kd))
    simp only [encKvIn, kvInV]
    iapply H
    ipureintro
    exact hk

theorem Start.wp_proof (c : w64) :
    {{ isPkgInit (PROP := IProp netDistGF) kit.pkg }}
      (App (Val (@! kit.startF)) (Val #c))
    {{ (d : w64), RET #d; True }} := by
  dsimp only [kit]
  wp_start
  wp_auto
  iapply HΦ $$ %_ %trivial

end gen

end orch

end Perennial.github_com.imdea_software.swiftpaxos
