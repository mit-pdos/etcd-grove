/-
`hraftnet.bootConfiguration`'s proof: the loop appending servers `1..n0`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.bootConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverID
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverAddr
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem bootConfiguration.wp_proof (wp_serverID : serverID.spec (GF := GF))
    (wp_serverAddr : serverAddr.spec (GF := GF)) : bootConfiguration.spec (GF := GF) := by
  intro n0 hn0
  wp_start as -
  wp_auto
  ihave HI : (∃ (k : w64) (sl : GoSlice), "i" ∷ i_ptr ↦ k ∗ "servers" ∷ servers_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* bootSrvs (uint.nat k - 1) ∗ "Hcap" ∷ ownSliceCap github_com.hashicorp.raft.Server sl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ n0 + 1⌝ : IProp GF) $$ [i servers]
  · iexists W64 1, slice.nil
    iframe
    rw [show bootSrvs (uint.nat (W64 1) - 1) = [] from rfl]
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_apply wp_serverID
    wp_apply wp_serverAddr
    have hk : W64 (((uint.nat k - 1 + 1 : Nat)) : Int) = k := by word
    wp_apply (wp_slice_literal (V := github_com.hashicorp.raft.Server) [srvOfK (uint.nat k - 1 + 1)])
    isplitr
    · ipureintro; simp only [srvOfK, hk]
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply (wp_slice_append (V := github_com.hashicorp.raft.Server)) $$ [$Hsl $Hcap $Hsl2] as %sl1 ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists k + W64 1, sl1
    have hii : uint.nat (k + W64 1) - 1 = (uint.nat k - 1) + 1 := by word
    rw [hii, bootSrvs_succ]
    iframe
    ipureintro; constructor <;> word
  · rw [show uint.nat k - 1 = n0 by word]
    iapply HΦ
    iframe

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
