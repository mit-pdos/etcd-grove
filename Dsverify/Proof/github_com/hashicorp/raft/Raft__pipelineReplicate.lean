/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__pipelineReplicate.lean (241f27e).
-/
/-
The proof of `Raft__pipelineReplicate` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pipelineReplicate
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pipelineSend
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pipelineDecode
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Dsverify.Proof.github_com.hashicorp.raft.ReplPipe
public import Perennial.Spec.fmt.Errorf
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond

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

theorem github_com.hashicorp.raft.Raft.pipelineReplicate.wp_proof
    (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_pipelineDecode : github_com.hashicorp.raft.Raft.pipelineDecode.spec (GF := GF) (hG := hG))
    (wp_pipelineSend : github_com.hashicorp.raft.Raft.pipelineSend.spec (GF := GF) (hG := hG))
    (wp_getLastLog : github_com.hashicorp.raft.raftState.getLastLog.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.pipelineReplicate.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s γs tid => by
  wp_start as ⟨#Hr, #Hs, #Hl, #Hlb, #Hstop, Hf, Htok⟩
  ihave ⟨#HcurT, ⟨%psf, #Hpeer⟩, #Hvj, #Hpl, -, ⟨%trig, #Htrig, #Htrigb⟩, -, -, ⟨%tde, #Htde, %γt, #Htdeb⟩, -⟩ :=
    replShared_core r γ i T j s $$ Hs
  ihave #Hcell := replShared_nextCell r γ rc i T j s $$ Hs
  unfold rwLock
  icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
  wp_auto_lc 1
  wp_apply wp_with_defer as %defer Hdefer
  imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
  wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP] as Hown
  imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
  ihave ⟨%x, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport
  icases Htr with ⟨-, -, -, -, -, -, #HAEP, -⟩
  wp_auto
  wp_bind (App (App (Val #(methods x.ty _ x.v)) _) _)
  iapply HAEP $$ %_ %j %T Hvj
  iintro %p %err Hres
  icases Hres with (⟨%Herr, %pI, %Hp, #Hpipe⟩ | ⟨#Herro, %c, #Hc⟩)
  rotate_left
  · -- no pipeline: return the error
    ihave %Herr := errOk_ne_nil err $$ Herro
    cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    iapply HΦ
    iframe Htok Hf
    iright
    isplitr; · iexact Herro
    iexists c; iexact Hc
  subst Herr Hp
  wp_auto
  -- the decoder's stop channel and the finish channel
  wp_apply (chan.wp_make1 (V := Unit)) as %sch %γc ⟨#Hsch, -, Hoc⟩
  imod (start_spsc sch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γc) $$ Hsch [Hoc]
    with ⟨%γst, #Hst, Hprod, Hscons⟩
  · ileft; iexact Hoc
  wp_apply (chan.wp_make1 (V := Unit)) as %fch %γc2 ⟨#Hfch, -, Hoc2⟩
  imod (fin_alloc fch γc2 (nextHalf s)) $$ Hfch Hoc2 with ⟨%γf, %Hγf, #Hfin, Hcl, Hftok⟩
  subst Hγf
  -- the decoder, with the writer's half of `nextIndex`
  icases replFields_elim s $$ Hf with ⟨%fv, %ap, %nv, Hfl, Hap, Hn⟩
  ipersist s
  ipersist r
  ipersist pipeline
  ipersist stopCh
  ipersist finishCh
  wp_func_lits
  wp_apply wp_goFunc $$ [$Hr $Htok Hscons Hcl Hn]
  · iintro %tid' Htok'
    wp_auto
    wp_apply (wp_pipelineDecode r γ rc i T j s pI sch fch γst γf tid') $$ [$Hr $Hs $Hpipe $Hfin $Hscons $Hcl $Htok' Hn] as Htok'
    · unfold hbStop; iframe #; unfold nextHalf; iexists _; iframe
    iframe; ipureintro; rfl
  iintro Htok
  wp_auto
  wp_apply (wp_loadUint64_cell wp_LoadUint64 s) $$ [$Hcell] as %nv0 -
  ihave HI : iprop(∃ (b : Bool), "shouldStop" ∷ shouldStop_ptr ↦ b ∗
      "Hfs" ∷ (finTok γf ∨ finDone γf ∗ nextHalf s) ∗
      "Hnx" ∷ (∃ v : w64, nextIndex_ptr ↦ v) ∗ "Htok" ∷ rtok tid) $$ [shouldStop Hftok nextIndex Htok]
  · iexists false; iframe
    isplitl [Hftok]; · ileft; iexact Hftok
    iexists _; iframe
  icases replStopCh_elim s γs $$ Hstop with ⟨%stc, #Hstc, #Hstopc⟩
  wp_for HI
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sdc, #Hsdc, %γsd, #Hsdbag⟩
  cases b
  · rw [if_pos (by simp)]
    wp_auto
    wp_apply (lc := 2) wp_config $$ [$Hr] as %c %Hc
    wp_apply wp_randomTimeout as %tch Htch
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the decoder finished
      ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, fch, γf.ch
      isplitr; · ipureintro; rfl
      isplitr; · iexact Hfch
      icases Hfs with (Hft | ⟨#Hd, Hh⟩)
      · iapply fin_rcv_tok_au $$ Hfin Hft
        inext
        iintro %u Hh #Hd
        wp_auto
        wp_for_post
        iframe
        iexists true
        iframe
        iright; iframe; iframe #
      · iapply fin_rcv_done_au $$ Hfin Hd
        inext
        iintro %u
        wp_auto
        wp_for_post
        iframe
        iexists true
        iframe
        iright; iframe; iframe #
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the stop channel (closed: the leader stepped down)
      ileft
      simp only [chan.blockingClausePre]
      iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs.ch
      isplitr; · ipureintro; rfl
      isplitr; · unfold stopChan; icases Hstopc with ⟨#Hc, -⟩; iexact Hc
      iapply stopChan_rcv_au $$ Hstopc Hlc1
      inext
      iintro %mi %_ok
      wp_auto
      wp_join iprop(∃ v : w64, nextIndex_ptr ↦ v ∗ rtok tid) with [Hnx Htok maxIndex]
      · icases Hnx with ⟨%nv1, Hnx⟩
        wp_apply (wp_pipelineSend r γ rc i T j s pI nextIndex_ptr mi tid) $$ [$Hr $Hs $Hl $Hlb $Hpipe $Htok Hnx]
          as %b' ⟨Htok, Hnx⟩
        · iexists _; iexact Hnx
        wp_join_done
        icases Hnx with ⟨%nv2, Hnx⟩
        iexists nv2; iframe
      iintro ⟨%v, Hnx, Htok⟩
      wp_auto
      wp_for_post
      iframe
      iexists true
      iframe
      iexists v; iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a `*deferError` of the leadership transfer
      ileft
      simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, tde, γt
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Htdeb
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htdeb
      inext
      iintro %d Hd
      wp_auto
      wp_apply (wp_getLastLog.2 r γ rc i) $$ [$Hr] as %li %lt -
      icases Hnx with ⟨%nv1, Hnx⟩
      wp_apply (wp_pipelineSend r γ rc i T j s pI nextIndex_ptr li tid) $$ [$Hr $Hs $Hl $Hlb $Hpipe $Htok Hnx]
        as %b' ⟨Htok, Hnx⟩
      · iexists _; iexact Hnx
      cases b'
      · wp_auto
        wp_apply (wp_respond d (fun _ => iprop(True)) _) $$ [Hd]
        · ileft; iframe
        iintro -
        wp_auto
        wp_for_post
        iframe
        iexists false
        iframe
      · wp_auto
        wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) as %e ⟨-, %s, -, He⟩
        · isplitl
          · iapply ownSlice_nil
          · iapply (fmt.argsOk_of_argsWf (by intro ii h; simp at h))
        wp_apply (wp_respond d (fun _ => iprop(True)) _) $$ [Hd]
        · ileft; iframe
        iintro -
        wp_auto
        wp_for_post
        iframe
        iexists true
        iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a trigger
      ileft
      simp only [chan.blockingClausePre]
      ihave ⟨%γn, #Hnb⟩ := notifyChan_bag trig $$ Htrigb
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, trig, γn
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hnb
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hnb
      inext
      iintro %u -
      wp_auto
      wp_apply (wp_getLastLog.2 r γ rc i) $$ [$Hr] as %li %lt -
      icases Hnx with ⟨%nv1, Hnx⟩
      wp_apply (wp_pipelineSend r γ rc i T j s pI nextIndex_ptr li tid) $$ [$Hr $Hs $Hl $Hlb $Hpipe $Htok Hnx]
        as %b' ⟨Htok, Hnx⟩
      · iexists _; iexact Hnx
      wp_for_post
      iframe
      iexists b'
      iframe
    iapply BigAndL.bigAndL_singleton.2
    -- the commit timeout
    icases Htch with (%Hnil | ⟨%γtm, #Htb⟩)
    · iright
      iapply chan.nilClausePre_recv time.Time _ _ Hnil
    · ileft
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γtm
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Htb
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htb
      inext
      iintro %u -
      wp_auto
      wp_apply (wp_getLastLog.2 r γ rc i) $$ [$Hr] as %li %lt -
      icases Hnx with ⟨%nv1, Hnx⟩
      wp_apply (wp_pipelineSend r γ rc i T j s pI nextIndex_ptr li tid) $$ [$Hr $Hs $Hl $Hlb $Hpipe $Htok Hnx]
        as %b' ⟨Htok, Hnx⟩
      · iexists _; iexact Hnx
      wp_for_post
      iframe
      iexists b'
      iframe
  · wp_if_destruct
    · exfalso; have := go.intoVal_inj Hif; simp at this
    rw [if_pos (by simp)]
    wp_auto
    wp_apply (lc := 2) (wp_spsc_close (V := Unit) γst sch _ _ []) $$ [$Hprod]
    · iframe #
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the decoder finished: the half of `nextIndex` comes back
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, fch, γf.ch
      isplitr; · ipureintro; rfl
      isplitr; · iexact Hfch
      icases Hfs with (Hft | ⟨#Hd, Hh⟩)
      · iapply fin_rcv_tok_au $$ Hfin Hft
        inext
        iintro %u Hh #Hd
        wp_auto
        unfold isPipeline
        icases Hpipe with ⟨-, -, #HClose⟩
        wp_bind (App (Val #(methods pI.ty _ pI.v)) _)
        iapply HClose
        wp_auto
        iapply HΦ
        iframe Htok
        iunfold nextHalf at Hh
        icases Hh with ⟨%nv2, Hh⟩
        isplitl [Hfl Hap Hh]; · iapply replFields_intro; iframe
        ileft; ipureintro; rfl
      · iapply fin_rcv_done_au $$ Hfin Hd
        inext
        iintro %u
        wp_auto
        unfold isPipeline
        icases Hpipe with ⟨-, -, #HClose⟩
        wp_bind (App (Val #(methods pI.ty _ pI.v)) _)
        iapply HClose
        wp_auto
        iapply HΦ
        iframe Htok
        iunfold nextHalf at Hh
        icases Hh with ⟨%nv2, Hh⟩
        isplitl [Hfl Hap Hh]; · iapply replFields_intro; iframe
        ileft; ipureintro; rfl
    iapply BigAndL.bigAndL_singleton.2
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdc, γsd
    isplitr; · ipureintro; rfl
    isplitr; · iapply is_bag_is_chan $$ Hsdbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsdbag
    inext
    iintro %u Hf
    iexfalso; iexact Hf

end proof

end Perennial
