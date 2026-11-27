/-
The proof of `rpctransport.Transport.Receiver`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__Receiver

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.Receiver.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.Receiver.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C
  wp_start as #Ht
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hs
  ipersist Hs
  imodintro
  iapply HΦ
  unfold isRcv
  iexists t
  iframe Hs Ht

end proof

end Perennial
