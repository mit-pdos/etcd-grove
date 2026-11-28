/-
`rserver.rnd`'s proof (hraft_robust; the copy of hraftnet's, `rnd.lean`): `RandomUint64() % n`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rserver.rnd
public import Perennial.Proof.github_com.goose_lang.primitive.Link
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.rserver

open github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem rnd.wp_proof : rnd.spec (GF := GF) := by
  intro n hn
  wp_start as -
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x -
  have hd : uint.Z n ≠ 0 := by omega
  simp only [hd, ↓reduceIte]
  wp_auto
  iapply HΦ
  ipureintro
  have h : (x % n).toNat < n.toNat := by
    rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (by word)
  word

end proof

end github_com.hashicorp.raft.examples.hraftnet.rserver

end Perennial
