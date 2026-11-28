/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__replicate.lean (241f27e).
-/
/-
The proof of `Raft__replicate` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__replicate
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__heartbeat
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__replicateTo
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pipelineReplicate
public import Dsverify.Proof.github_com.hashicorp.raft.ReplPipe
public import Perennial.Spec.fmt.Errorf
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout

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

theorem github_com.hashicorp.raft.Raft.replicate.wp_proof
    (wp_heartbeat : github_com.hashicorp.raft.Raft.heartbeat.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_replicateTo : github_com.hashicorp.raft.Raft.replicateTo.spec (GF := GF) (hG := hG))
    (wp_pipelineReplicate : github_com.hashicorp.raft.Raft.pipelineReplicate.spec (GF := GF) (hG := hG))
    (wp_getLastLog : github_com.hashicorp.raft.raftState.getLastLog.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.replicate.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T s tid => by
  wp_start as ⟨#Hr, Hown, Htok⟩
  icases replOwn_fields r γ rc i T s $$ Hown with ⟨%j, #Hs, #Hl, #Hlb, ⟨%γs, #Hstop⟩, Hf⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (chan.wp_make1 (V := Unit)) as %hch %γc ⟨#Hhch, -, Hoc⟩
  imod (start_spsc hch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γc) $$ Hhch [Hoc]
    with ⟨%γh, #Hhb, Hprod, Hhcons⟩
  · ileft; iexact Hoc
  ipersist stopHeartbeat
  ipersist s
  ipersist r
  wp_func_lits
  wp_apply wp_goFunc $$ [$Hr $Htok Hhcons]
  · iintro %tid' Htok'
    wp_auto
    wp_apply wp_heartbeat $$ [$Hr $Hs $Hl $Hlb $Htok' Hhcons] as Htok'
    · unfold hbStop; iframe #; iframe
    iframe; ipureintro; rfl
  iintro Htok
  wp_auto
  wp_for
  ihave HI : iprop(∃ (b : Bool), "shouldStop" ∷ shouldStop_ptr ↦ b ∗
      "Hf" ∷ replFields s ∗ "Htok" ∷ rtok tid) $$ [shouldStop Hf Htok]
  · iexists false; iframe
  wp_for HI
  wp_if_destruct
  rotate_left
  · -- the inner loop ends: stop
    have hb : b = true := by
      cases b
      · exfalso; exact Hif rfl
      · rfl
    subst hb
    simp
    wp_auto
    wp_for_post
    wp_apply (wp_spsc_close (V := Unit) γh hch _ _ []) $$ [$Hprod]
    · iframe #
    iapply HΦ $$ Htok
  have hb : b = false := by
    have := go.intoVal_inj Hif; cases b <;> simp_all
  subst hb
  ihave ⟨-, -, -, -, -, ⟨%trig, #Htrig, #Htrigb⟩, -, -, ⟨%tde, #Htde, %γt, #Htdeb⟩, -⟩ := replShared_core r γ i T j s $$ Hs
  ihave ⟨%stc, #Hstc, #Hstopc⟩ := replStopCh_elim s γs $$ Hstop
  -- one of: the stop channel's close, a trigger, the commit timeout
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ b' : Bool, shouldStop_ptr ↦ b' ∗
      replFields s ∗ rtok tid) ∨
      (⌜v = returnVal #()⌝ ∗ replFields s ∗ rtok tid))) at next with [shouldStop Hf Htok]
  · wp_auto
    wp_apply (lc := 2) wp_config $$ [$Hr] as %c %Hc
    wp_apply wp_randomTimeout as %tch Htch
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the stop channel: closed (nothing is ever sent on it)
      ileft
      simp only [chan.blockingClausePre]
      iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs.ch
      isplitr; · ipureintro; rfl
      isplitr
      · unfold stopChan; icases Hstopc with ⟨#Hc, -⟩; iexact Hc
      iapply stopChan_rcv_au $$ Hstopc Hlc1
      inext
      iintro %mi %_ok
      wp_auto
      wp_if_destruct
      · -- best effort up to `maxIndex` (a removed server: not in scope, but harmless)
        wp_apply (wp_replicateTo r γ rc i T j s γs mi tid) $$ [$Hr $Hs $Hl $Hlb $Hstop $Hf $Htok]
          as %b' ⟨Htok, Hf⟩
        iright; iframe; ipureintro; rfl
      · iright; iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a `*deferError` of the leadership transfer: replicate, then answer it
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
      wp_apply (wp_replicateTo r γ rc i T j s γs li tid) $$ [$Hr $Hs $Hl $Hlb $Hstop $Hf $Htok]
        as %b' ⟨Htok, Hf⟩
      cases b'
      · wp_auto
        wp_apply (wp_respond d (fun _ => iprop(True)) _) $$ [Hd]
        · ileft; iframe
        iintro -
        wp_auto
        ileft
        isplitr; · ipureintro; rfl
        iexists false; iframe
      · wp_auto
        ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
        · first | iPkgInit | iframe
        wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [$HfmtS] as %e -
        · isplitr
          · iapply ownSlice_nil
          · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (by intro ii h; simp at h))
        wp_apply (wp_respond d (fun _ => iprop(True)) _) $$ [Hd]
        · ileft; iframe
        iintro -
        wp_auto
        ileft
        isplitr; · ipureintro; rfl
        iexists true; iframe
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
      wp_apply (wp_replicateTo r γ rc i T j s γs li tid) $$ [$Hr $Hs $Hl $Hlb $Hstop $Hf $Htok]
        as %b' ⟨Htok, Hf⟩
      ileft
      isplitr; · ipureintro; rfl
      iexists b'; iframe
    iapply BigAndL.bigAndL_singleton.2
    -- the commit timeout
    icases Htch with (%Hnil | ⟨%γt, #Htb⟩)
    · iright
      iapply chan.nilClausePre_recv time.Time _ _ Hnil
    · ileft
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Htb
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htb
      inext
      iintro %u -
      wp_auto
      wp_apply (wp_getLastLog.2 r γ rc i) $$ [$Hr] as %li %lt -
      wp_apply (wp_replicateTo r γ rc i T j s γs li tid) $$ [$Hr $Hs $Hl $Hlb $Hstop $Hf $Htok]
        as %b' ⟨Htok, Hf⟩
      ileft
      isplitr; · ipureintro; rfl
      iexists b'; iframe
  iintro HQ
  icases HQ with (⟨%Hv, %b', shouldStop, Hf, Htok⟩ | ⟨%Hv, Hf, Htok⟩)
  rotate_left
  · -- the stop channel was closed: return
    subst Hv
    wp_auto
    wp_for_post
    wp_for_post
    wp_apply (wp_spsc_close (V := Unit) γh hch _ _ []) $$ [$Hprod]
    · iframe #
    iapply HΦ $$ Htok
  subst Hv
  wp_auto
  cases b'
  rotate_left
  · -- `replicateTo` asked to stop: the inner loop ends
    wp_auto
    wp_for_post
    iframe
    iexists true; iframe
  icases replFields_elim s $$ Hf with ⟨%fv, %ap, %nv, Hfl, Hap, Hn⟩
  wp_auto
  cases ap
  · -- no pipelining yet: the inner loop goes on
    wp_auto
    ihave Hf := replFields_intro s fv false nv $$ [Hn Hfl Hap]
    · iframe
    wp_for_post
    iframe
    iexists false
    iframe
  -- pipelining allowed: pipeline mode until it stops
  wp_auto
  wp_for_post
  ihave Hf := replFields_intro s fv false nv $$ [Hn Hfl Hap]
  · iframe
  wp_apply (lc := 1) (wp_pipelineReplicate r γ rc i T j s γs tid) $$ [$Hr $Hs $Hl $Hlb $Hstop $Hf $Htok]
    as %err ⟨Htok, Hf, Herr⟩
  icases Herr with (%Herr | Herro)
  · subst Herr
    wp_auto
    wp_for_post
    iframe
  icases Herro with ⟨#Herro, %c, #Hce⟩
  ihave %Hne := errOk_ne_nil err $$ Herro
  ihave ⟨%x, %Hx⟩ := isRaftErr_ptr c err $$ Hce
  subst Hx
  ihave ⟨%e0, #He0⟩ := isRaftErr_of_init (GF := GF) .pipelineReplicationNotSupported $$ Hpkg
  ihave #Hg0 := isRaftErr_global .pipelineReplicationNotSupported e0 $$ He0
  ihave ⟨%x0, %Hx0⟩ := isRaftErr_ptr .pipelineReplicationNotSupported e0 $$ He0
  subst Hx0
  simp only [RaftErr.var] at *
  wp_auto
  wp_if_destruct
  · wp_for_post
    iframe
  · ihave ⟨-, -, -, #Hpl, -⟩ := replShared_core r γ i T j s $$ Hs
    unfold rwLock
    icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
    imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
    wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
    wp_apply +noauto (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP]
    iintro Hown
    imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
    wp_auto
    wp_for_post
    iframe


end proof

end Perennial
