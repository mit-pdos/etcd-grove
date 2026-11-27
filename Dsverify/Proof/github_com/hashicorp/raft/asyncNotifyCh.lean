/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/asyncNotifyCh.lean (241f27e).
-/
/-
The proof of `raft.asyncNotifyCh`: a non-blocking send on a bag channel (the value's resource
`P ()` goes into the bag if the send happens, is dropped otherwise).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh

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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.asyncNotifyCh.wp_proof :
    github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG) :=
  fun γc ch P => by
  wp_start as ⟨#Hbag, HP⟩
  wp_auto_lc 2
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    dsimp only [chan.nonblockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    ihave #Hch := is_bag_is_chan _ _ _ $$ Hbag
    iframe Hch
    iapply blocking_send_implies_nonblocking
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag HP
    inext
    wp_auto
    iapply HΦ; itrivial
  · wp_auto
    iapply HΦ; itrivial

end proof

end Perennial
