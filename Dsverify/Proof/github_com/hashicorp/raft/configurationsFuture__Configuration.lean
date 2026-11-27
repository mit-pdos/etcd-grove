/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/configurationsFuture__Configuration.lean (241f27e).
-/
/-
The proof of `raft.configurationsFuture.Configuration` (stage 4 interface: a new spec, to be proved).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.configurationsFuture__Configuration

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

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

theorem github_com.hashicorp.raft.configurationsFuture.Configuration.wp_proof : github_com.hashicorp.raft.configurationsFuture.Configuration.spec (GF := GF) (hG := hG) := by
  intro f cf dq
  wp_start as Hcf
  icases typedPointsto_not_null_dup _ _ _ $$ Hcf with ⟨Hcf, %Hn⟩
  iStructNamed Hcf
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
