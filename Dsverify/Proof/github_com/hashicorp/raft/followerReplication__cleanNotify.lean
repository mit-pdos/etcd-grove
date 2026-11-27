/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/followerReplication__cleanNotify.lean (241f27e).
-/
/-
The proof of `followerReplication__cleanNotify` (replication subsystem, stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__cleanNotify
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify

@[expose] public section

set_option linter.unusedVariables false
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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.followerReplication.cleanNotify.wp_proof :
    github_com.hashicorp.raft.followerReplication.cleanNotify.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s v => by
  wp_start as #Hs
  ihave ⟨%vch, #Hvch, #Hnl⟩ := replShared_notify r γ rc i T j s $$ Hs
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hnl] as ⟨Hlocked, Hinv⟩
  iunfold notifyInv at Hinv
  icases Hinv with ⟨%m, %M, Hn, Hm, HM⟩
  wp_auto
  wp_apply (wp_mapDelete (K := Loc) (V := Unit) m M v (go.GoType.PointerType verifyFuture.ty)
    (go.GoType.StructType [])) $$ [$Hm] as Hm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hnl $Hlocked Hn Hm HM]
  · inext
    unfold notifyInv
    iexists m, _
    iframe
    iapply (BigSepM.bigSepM_subseteq (Φ := fun v (_ : Unit) => notifyEntry γ rc i T vch j v)
      Iris.Std.LawfulPartialMap.delete_subset_self) $$ HM
  iapply HΦ; itrivial

end proof

end Perennial
