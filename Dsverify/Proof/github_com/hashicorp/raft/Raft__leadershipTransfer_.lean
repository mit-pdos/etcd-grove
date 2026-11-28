/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__leadershipTransfer_.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).leadershipTransfer` (stage 2): the leadership transfer goroutine.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__leadershipTransfer_
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Futures
public import Perennial.Spec.sync.atomic.LoadUint64
public import Perennial.Spec.fmt.Errorf
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

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 2000000 in
theorem github_com.hashicorp.raft.Raft.leadershipTransfer.wp_proof
    (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_ErrorfE : fmt.Errorf.spec_tnErr (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.leadershipTransfer.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j id repl stopCh doneCh γst γd Pst tid => by
  wp_start as ⟨#Hr, #Hsh, #Hstop, #Hdone, Htok⟩
  wp_auto
  ipersist r; ipersist doneCh; ipersist stopCh; ipersist repl; ipersist address; ipersist id
  ihave #Hstch := ownBroadcastChan_is_chan _ _ _ _ $$ Hstop
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply (chan.wp_select_nonblocking_alt [iprop(True)] iprop(rtok tid ∗ (rtok tid -∗ Φ #())))
    $$ [] [Htok HΦ] []
  · iapply BigSepL2.bigSepL2_cons.2
    isplitl
    · iintro ⟨Htok, HΦ⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stopCh, γst
      isplit; · ipureintro; rfl
      isplit; · iexact Hstch
      iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ .Unknown $$ Hstop
      dsimp only
      isplit
      · iintro -
        wp_auto
        wp_apply (wp_bag_send γd doneCh interface.nil (fun _ => iprop(True))) $$ [$Hdone]
        iapply HΦ; iframe
      · iintro -; iframe
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
  · iframe
  iintro ⟨Htok, HΦ⟩ -
  wp_auto
  ihave #Hni := replShared_nextCell r γ rc i T j repl $$ Hsh
  unfold nextCell
  unfold replShared
  icases Hsh with ⟨%cm, %stc, %trig, %notif, %sd, %tde, %γs, -, -, #Hjv, %Hji, -, -, -, -, -, -, -,
    -, -, -, -, #Htdef, ⟨%γt, #Htdb⟩, -, -, -⟩
  wp_for
  wp_apply (wp_LoadUint64 _ (DFrac.own (1 : Qp).half))
  iinv Hni with ⟨%x, Hx⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑nextIdxN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists x
  iframe Hx
  iintro Hx
  imod Hmask
  imod Hclose $$ [Hx]
  · inext; iexists x; iframe
  imodintro
  wp_auto
  wp_apply (wp_getLastIndex.2 r γ rc i) $$ [$Hr] as %li -
  wp_if_destruct
  · iStructNamed «$r0»
    wp_apply (wp_deferError_init «$r0_ptr» (fun _ => iprop(True)) _) $$ [$errCh]
      as ⟨%ch, %γe, %Hne, HerrCh, #Hspsc, Hprod, Hcons⟩
    ipersist HerrCh
    wp_apply (lc := 2) (wp_bag_send γt tde «$r0_ptr» (fun d => deferResp d (fun _ => iprop(True))))
      $$ [$Htdb Hprod responded]
    · unfold deferResp
      iexists ch
      isplitr; · iexact HerrCh
      iright; iexists γe; iframe; iframe #; ipureintro; exact Hne
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
      isplitr; · ipureintro; rfl
      isplitr
      · unfold isSpsc; icases Hspsc with ⟨$, -⟩
      iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
      inext
      iintro %v %ok -
      wp_auto
      cases v with
      | nil =>
        wp_auto
        wp_for_post
        iframe
      | ok e =>
        wp_auto
        wp_apply (wp_bag_send γd doneCh (GoInterface.ok e) (fun _ => iprop(True))) $$ [$Hdone]
        wp_for_post
        iapply HΦ; iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stopCh, γst
      isplitr; · ipureintro; rfl
      isplitr; · iexact Hstch
      iapply broadcast_chan_receive _ _ _ _ .Unknown $$ Hstop
      iintro -
      wp_auto
      wp_apply (wp_bag_send γd doneCh interface.nil (fun _ => iprop(True))) $$ [$Hdone]
      wp_for_post
      iapply HΦ; iframe
    iapply BigAndL.bigAndL_nil.2; itrivial
  · rw [if_neg (by intro h; apply Hif; simp_all)]
    wp_auto
    wp_apply (wp_getRPCHeader r γ rc i) $$ [$Hr] as %h #Hh
    ihave ⟨%trI, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
    unfold isTransport
    icases Htr with ⟨#Hrpc, #HConsumer, #HLocalAddr, #HEncodePeer, #HDecodePeer, #HSetHB, #HAEP, #HAE,
      #HRV, #HRPV, #HIS, #HTN⟩
    wp_auto
    wp_apply HTN $$ [] [$«$a2»] [] [$«$a3»] [$Htok] as %err Hargs Htok Hres
    · iexact Hjv
    · unfold tnReq; iexact Hh
    icases Hres with (⟨%Herr, -⟩ | ⟨#Herr, %Hnf, -⟩)
    · subst Herr
      wp_auto
      wp_apply (wp_bag_send γd doneCh interface.nil (fun _ => iprop(True))) $$ [$Hdone]
      iapply HΦ; iframe
    · ihave %Hne := errOk_ne_nil err $$ Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok e =>
        obtain ⟨xe, hx, Hfmt, HErrSig⟩ := Hnf
        cases hx
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any)
          [interface.mkOk ServerID.ty #id, GoInterface.ok e]
        wp_auto
        isplitl []; · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_auto
        wp_apply (wp_ErrorfE _ id e Hfmt HErrSig) $$ [$Hasl $Herr] as %e2 #He2
        wp_apply (wp_bag_send γd doneCh (interface.ok e2) (fun _ => iprop(True))) $$ [$Hdone]
        iapply HΦ; iframe

end proof

end Perennial
