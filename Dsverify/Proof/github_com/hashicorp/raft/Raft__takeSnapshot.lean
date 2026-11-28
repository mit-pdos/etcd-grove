/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__takeSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).takeSnapshot` (stage 3): the FSM goroutine's snapshot, the main loop's
configurations, the sink's commit (`snapProof.own_commit`), the last snapshot, the compaction.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__takeSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogs
public import Dsverify.Spec.github_com.hashicorp.raft.getSnapshotVersion
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.SnapBase
public import Dsverify.Proof.github_com.hashicorp.raft.FmtErrorf

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem github_com.hashicorp.raft.Raft.takeSnapshot.wp_proof
    (wp_setLastSnapshot : github_com.hashicorp.raft.raftState.setLastSnapshot.spec (GF := GF) (hG := hG))
    (wp_compactLogs : github_com.hashicorp.raft.Raft.compactLogs.spec (GF := GF) (hG := hG))
    (wp_getSnapshotVersion : github_com.hashicorp.raft.getSnapshotVersion.spec (GF := GF) (hG := hG))
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.takeSnapshot.spec (GF := GF) (hG := hG) :=
  fun r γ rc i tid => by
  wp_start as ⟨#Hr, Htok⟩
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γs, #Hsbag⟩
  ihave ⟨%fsch, %γf, #Hfsch, #Hfbag⟩ := isRaft_fsmSnapshotCh r γ rc i $$ Hr
  ihave ⟨%cch, %γq, #Hcch, #Hcbag⟩ := isRaft_configurationsCh r γ rc i $$ Hr
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  irename «$r0» => Hf
  generalize «$r0_ptr» = f at *
  iStructNamed Hf
  try simp only [zeroValDef] at *
  iStructNamed deferError
  wp_apply (lc := 2) snapFut.wp_sf_init f (snapReqQ γ rc f) null $$ [$errCh]
    as ⟨%ech, %γe, %Hne, HerrCh, #Hspsc, HeP, HeC⟩
  ipersist HerrCh
  ipersist ShutdownCh
  ihave #HnnE := isRaftErr_of_init RaftErr.nothingNewToSnapshot $$ Hpkg
  icases HnnE with ⟨%eNN, #HeNN⟩
  ihave #HgNN := isRaftErr_global RaftErr.nothingNewToSnapshot eNN $$ HeNN
  dsimp only [RaftErr.var]
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the send on fsmSnapshotCh
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, fsch, γf, f
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply is_bag_is_chan $$ Hfbag
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hfbag [index term snapshot responded HeP]
    · unfold snapReqP
      isplitl [index term snapshot]
      · iexists _, _, _; iframe
      unfold deferResp
      iexists ech
      iframe HerrCh
      iright
      iexists γe
      iframe
      iframe #
      ipureintro; exact Hne
    inext
    wp_auto
    wp_apply snapFut.wp_sf_Error wp_Error f (snapReqQ γ rc f) $$ [HeC err] as %serr Hq
    · unfold deferWait
      iexists ech, γe
      iframe HerrCh Hspsc HeC err
      isplitr
      · ipureintro; exact Hne
      iexists _; iframe ShutdownCh; ileft; ipureintro; rfl
    unfold snapReqQ
    icases Hq with (⟨%Hse, %x, %tx, %mb, %snap, index, term, snapshot, %Hx1, #Hbe, ⟨%ex, #HCx, %Hex⟩, #HsOk⟩ |
      ⟨#Hnn, %x0, %tx0, %sn0, index, term, snapshot⟩)
    · subst Hse
      wp_auto
      irename «$r0» => Hcf
      generalize «$r0_ptr» = g at *
      iStructNamed Hcf
      try simp only [zeroValDef] at *
      iStructNamed deferError
      wp_apply (lc := 2) snapFut.wp_cf_init g (cfgReqQ γ rc i g x) null $$ [$errCh]
        as ⟨%gch, %γg, %Hgne, HgCh, #Hgspsc, HgP, HgC⟩
      ipersist HgCh
      ipersist ShutdownCh
      ihave #HsOk' := HsOk
      unfold fsmSnapOk
      icases HsOk' with ⟨#HPersist, #HRelease⟩
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, cch, γq, g
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        isplitr
        · iapply is_bag_is_chan $$ Hcbag
        iapply bag_send_au $$ [$Hlc1 $Hlc2] Hcbag [configurations responded HgP]
        · unfold cfgReqP
          iexists x, mb
          iframe Hbe
          isplitr
          · ipureintro; exact Hx1
          isplitl [configurations]
          · iexists _; iframe
          unfold deferResp
          iexists gch
          iframe HgCh
          iright
          iexists γg
          iframe
          iframe #
          ipureintro; exact Hgne
        inext
        wp_auto
        wp_apply snapFut.wp_cf_Error wp_Error g (cfgReqQ γ rc i g x) $$ [HgC err] as %cerr Hq
        · unfold deferWait
          iexists gch, γg
          iframe HgCh Hgspsc HgC err
          isplitr
          · ipureintro; exact Hgne
          iexists _; iframe ShutdownCh; iright; unfold deadChan; iexists γs; iexact Hsbag
        unfold cfgReqQ
        icases Hq with (⟨%Hce, %cf, configurations, ⟨%ss, #Hcv, #Hcor⟩, #Hdx, #Hax, #Hcx⟩ |
          ⟨#Hlt, %cf, configurations⟩)
        · subst Hce
          imod durLb_lt γ ⊤ (by simp) i x $$ [$HI $Hvi $Hdx] with %Hx62
          imod snapProof.CIdx_term_lt γ ⊤ (by simp) x ex $$ [$HI $HCx] with %Hex62
          wp_auto
          wp_if_destruct
          · -- (stage 4) the committed configuration's index is above the snapshot's: the new error
            wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
              (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := GoInterface) (t := go.any)
              [interface.mkOk go.uint64 #cf.committedIndex', interface.mkOk go.uint64 #(W64 (x : Int))]
            wp_auto
            isplitl []; · ipureintro; rfl
            iintro %asl ⟨Hasl, -⟩
            wp_auto
            wp_apply (fmt.wp_Errorf_snapCfgErr _ _ _) $$ [$Hasl] as %ex2 -
            wp_apply HRelease
            iapply HΦ; iframe; iright; iright; iright; ipureintro; exact ⟨ex2, rfl⟩
          icases Hcor with (%Hcl | #Hsnc)
          · exfalso
            apply Hif
            word
          ihave #Himm := isRaft_imm r γ rc i $$ Hr
          unfold raftImm
          icases Himm with ⟨#Hpv, -⟩
          wp_auto
          wp_apply wp_getSnapshotVersion
          ihave ⟨%ssx, %eof', #Hssf, #HSS, -⟩ := isRaft_snapshotStore r γ rc i $$ Hr
          ihave #Hsc := isRaft_durInv r γ rc i $$ Hr
          unfold isSnapStore
          icases HSS with ⟨#HCreate, -, -⟩
          ihave ⟨%xtr, %rpcCh, #Htr, -, -⟩ := isRaft_transport r γ rc i $$ Hr
          wp_auto
          wp_bind
          iapply HCreate
          iintro %k %sid Hcont
          imod Hcont $$ %(fun _ => iprop(True)) %(fun _ => latLb rc x) [] with ⟨%own, #Hsink, Hown⟩
          · iintro %bs %Hbs Hwin -
            iunfold snapWin at Hwin
            ihave ⟨Hlat, -⟩ := Hwin $$ []
            · ipureintro; exact Hbs
            iapply snapProof.own_commit γ rc i x tx sid cf.committed' cf.committedIndex' bs ex Hx1 Hx62 Hex
              (by rw [← Hex]; exact Hex62)
            iframe # ∗
          wp_auto
          wp_bind
          iapply HPersist $$ %k %sid %own
            %(fun bs => iprop(snapWin γ rc i (sinkMeta (W64 1) (W64 x) (W64 tx) cf.committedIndex' cf.committed' sid bs) bs ∗ True))
            %(fun _ => latLb rc x) Hsink [] Hown
          · iintro !> %b0 H
            isplitl; rotate_left; · itrivial
            unfold snapWin
            iintro %Hb0
            isplitl
            · iapply snapProof.own_latestOk γ rc x tx sid cf.committed' cf.committedIndex' ss b0 ex Hx1 Hx62 Hex
                (by rw [← Hex]; exact Hex62) Hb0
              iframe # ∗
            ileft
            simp only [sinkMeta]
            rw [show uint.nat (W64 (x : Int)) = x by word]
            iexact Hdx
          iintro Hown ⟨%bL, #HlatLb⟩
          wp_auto
          ihave #Hsink' := Hsink
          unfold isSink
          icases Hsink' with ⟨-, -, -, #HClose2, -, #HID⟩
          wp_bind
          iapply HClose2 $$ Hown
          iintro Hown
          wp_auto
          have hx' : uint.nat (W64 (x : Int)) = x := by word
          have htx' : uint.nat (W64 (tx : Int)) = tx := by rw [← Hex]; word
          wp_apply wp_setLastSnapshot r γ rc i (W64 x) (W64 tx) $$ [$Hr]
          · iright; iexists ex
            rw [hx', htx']
            iframe HCx Hax
            isplitr
            · ipureintro; exact Hex
            ileft; iexact Hdx
          wp_apply wp_compactLogs r γ rc i (W64 x) tid $$ [$Hr $Htok] as %cerr ⟨%Hce, Htok⟩
          · rw [hx']; iframe Hcx HlatLb Hdx; ipureintro; exact Hx62
          subst Hce
          wp_auto
          wp_apply HID
          wp_apply HRelease
          iapply HΦ; iframe; ileft; ipureintro; rfl
        · ihave ⟨%ex, %Hex⟩ := snapProof.raftErr_shape _ _ $$ Hlt
          subst Hex
          wp_auto
          wp_apply HRelease
          iapply HΦ; iframe; iright; iright; ileft; iexact Hlt
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γs
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Hsbag
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsbag
        inext
        iintro %t Hf
        iexfalso; iexact Hf
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · -- nothing new to snapshot
      ihave %Hagr := isRaftErr_agree RaftErr.nothingNewToSnapshot serr eNN $$ [$Hnn $HeNN]
      subst Hagr
      ihave ⟨%ex, %Hex⟩ := snapProof.raftErr_shape _ _ $$ Hnn
      subst Hex
      wp_auto
      iapply HΦ; iframe; iright; ileft; iexact Hnn
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- shutdownCh: never closed, never sent on
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hsbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsbag
    inext
    iintro %t Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial
