/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__config.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).config`: the `atomic.Value` `conf`, read-only since `NewRaft`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.config.wp_proof :
    github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #His
  ihave ⟨%c, #Hv, %Hc⟩ := isRaft_config r γ rc i $$ His
  wp_auto
  wp_apply_core sync.atomic.Value.wp_Load _ DFrac.discard $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Hv
  iintro _
  imod Hmask with -
  imodintro
  wp_auto
  iapply HΦ
  ipureintro; exact Hc

end proof

end Perennial
