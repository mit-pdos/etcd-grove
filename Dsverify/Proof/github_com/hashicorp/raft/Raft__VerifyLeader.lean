/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__VerifyLeader.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).VerifyLeader` (stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__VerifyLeader
public import Dsverify.Proof.github_com.hashicorp.raft.FutBase

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

theorem github_com.hashicorp.raft.Raft.VerifyLeader.wp_proof :
    github_com.hashicorp.raft.Raft.VerifyLeader.spec (GF := GF) (hG := hG) := by
  intro r γ rc i sc
  wp_start as ⟨#Hr, #Hsc⟩
  wp_auto
  ihave Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans deadField deadChan
  icases Hch with ⟨-, ⟨%vch, #Hvch, %γv, #Hbag⟩, -, -, -, -, -, -, -, ⟨%sdCh, #HsdCh, %γsd, #Hsd⟩, -⟩
  irename «$r0» => Hf
  generalize «$r0_ptr» = f at *
  iStructNamed Hf
  try simp only [zeroValDef] at *
  iStructNamed deferError
  wp_apply (lc := 2) futProof.wp_vf_init f (verifyQ γ rc i sc) null $$ [$errCh]
    as ⟨%ch, %γe, %Hne, HerrCh, #Hspsc, Hprod, Hcons⟩
  ipersist HerrCh
  ipersist ShutdownCh
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- shutdownCh: never closed, never sent on
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdCh, γsd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hsd
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsd
    inext
    iintro %t Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the send on verifyCh
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, vch, γv, f
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag [notifyCh quorumSize votes voteLock responded Hprod]
    · unfold verifyP
      ileft
      unfold verifyNew
      iexists sc
      iframe
      iframe #
      unfold deferResp
      iexists ch
      iframe #
      iright
      iframe
      ipureintro; exact Hne
    inext
    wp_auto
    iapply HΦ
    unfold futWait
    iright; iright; ileft
    iexists f
    isplitr
    · ipureintro; rfl
    unfold deferWait
    iexists ch, γe
    iframe
    iframe #
    rw [show (chan.nil : GoChan) = null from rfl]
    iframe #
    isplitr; · ipureintro; exact Hne
    ileft; ipureintro; rfl
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial
