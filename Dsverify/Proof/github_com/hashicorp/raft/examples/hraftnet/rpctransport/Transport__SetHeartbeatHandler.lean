/-
The proof of `rpctransport.Transport.SetHeartbeatHandler`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__SetHeartbeatHandler
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.SetHeartbeatHandler.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.SetHeartbeatHandler.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C cb
  wp_start as ⟨#Ht, #Hh⟩
  unfold isTrans
  iNamed Ht
  wp_auto
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
  iunfold hbInv at Hinv
  icases Hinv with ⟨%f, Hf, -⟩
  wp_auto
  wp_apply wp_Unlock $$ [$Hmu $Hlk Hf]
  · inext; unfold hbInv; iexists cb; iframe Hf; iright; iexact Hh
  iapply HΦ; itrivial

end proof

end Perennial
