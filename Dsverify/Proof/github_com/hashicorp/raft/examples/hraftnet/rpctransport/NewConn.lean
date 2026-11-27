/-
The proof of `rpctransport.NewConn`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn.spec (GF := GF) (hG := hG) := by
  intro W a
  wp_start as ⟨#Hra, %Hrb⟩
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hp
  iStructNamed Hp
  ipersist addr
  imod sync.init_Mutex (connInv W a «$r0_ptr») ⊤ _ $$ mu [c] with #Hmu
  · inext
    unfold connInv
    iexists _
    iframe c
    ileft; ipureintro; rfl
  imodintro
  iapply HΦ
  unfold isConn
  iframe Hmu Hra addr
  ipureintro; exact Hrb

end proof

end Perennial
