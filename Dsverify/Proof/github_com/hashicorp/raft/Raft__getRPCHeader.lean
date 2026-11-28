/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__getRPCHeader.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).getRPCHeader`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config

@[expose] public section

set_option linter.deprecated false

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

theorem github_com.hashicorp.raft.Raft.getRPCHeader.wp_proof
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG) :=
  fun r γ rc i => by
  wp_start as #Hr
  wp_auto
  ihave ⟨%x, %rpcCh, #Htr, #HrpcCh, #Ht⟩ := isRaft_transport r γ rc i $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, -, #Hla, -⟩
  unfold isTransport
  icases Ht with ⟨-, -, -, #Henc, -⟩
  wp_apply wp_config $$ [$Hr] with %c %Hc
  wp_apply wp_config $$ [$Hr] with %c2 %Hc2
  wp_apply (wp_string_to_bytes c2.LocalID') with %sl1 ⟨Hsl1, -⟩
  wp_apply wp_config $$ [$Hr] with %c3 %Hc3
  ipersist Hsl1
  wp_apply +noauto Henc with %sl2 Hsl2
  ipersist Hsl2
  wp_auto
  iapply HΦ
  unfold hdrOk
  obtain ⟨hpv, hid, -⟩ := Hc
  obtain ⟨-, hid2, -⟩ := Hc2
  simp only [hid2]
  iframe #
  ipureintro; exact hpv

end proof

end Perennial
