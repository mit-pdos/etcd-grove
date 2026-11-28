/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/RPC__Respond.lean (241f27e).
-/
/-
The proof of `raft.(*RPC).Respond`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond

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

theorem github_com.hashicorp.raft.RPC.Respond.wp_proof :
    github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG) :=
  fun p v γc P resp err => by
  wp_start as ⟨Hp, #Hbag, HP⟩
  wp_auto
  wp_apply wp_bag_send γc v.RespChan' (RPCResponse.mk resp err) P $$ [$Hbag $HP]
  wp_end
