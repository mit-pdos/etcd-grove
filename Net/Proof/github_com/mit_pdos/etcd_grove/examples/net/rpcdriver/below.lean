/- Lean-first (no Rocq counterpart).

# `below`'s proof
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

theorem below.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    below.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as -
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    ipureintro
    constructor
    · intro; rfl
    · intro h; exact absurd rfl h
  · wp_apply wp_RandomUint64 as %x -
    have hz : uint.Z n ≠ 0 := by intro h; apply Hif; word
    simp only [hz, ↓reduceIte]
    wp_auto
    iapply HΦ
    ipureintro
    constructor
    · intro h; exact absurd h Hif
    · intro _
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n.toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) Hif
        · exact h
      have := BitVec.umod_lt x hn
      word

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
