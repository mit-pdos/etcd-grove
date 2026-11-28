/-
The proof of `rpctransport.appendFuture.Error` (ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture__Error

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Error.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Error.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start as #Hd
  unfold futDone
  icases Hd with ⟨%dc, %γd, #Hdone, #Hb⟩
  wp_auto
  wp_apply chan.wp_receive dc γd $$ [] as Hrcv
  · iapply ownBroadcastChan_is_chan $$ Hb
  iapply broadcast_chan_receive $$ Hb
  iintro ⟨#HQ, -⟩
  unfold futErrDone
  icases HQ with ⟨%e, #He, #Hok⟩
  wp_auto
  wp_end


end proof

end Perennial
