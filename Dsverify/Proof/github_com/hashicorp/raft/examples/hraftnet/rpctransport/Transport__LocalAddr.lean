/-
The proof of `rpctransport.Transport.LocalAddr`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__LocalAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.LocalAddr.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.LocalAddr.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C
  wp_start as #Ht
  unfold isTrans
  iNamed Ht
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
