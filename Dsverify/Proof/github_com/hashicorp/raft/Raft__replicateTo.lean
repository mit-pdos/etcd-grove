/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__replicateTo.lean (241f27e).
-/
/-
The proof of `Raft__replicateTo` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__replicateTo
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupAppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__sendLatestSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.appendStats
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__handleStaleTerm
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.updateLastAppended
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
public import Dsverify.Spec.github_com.hashicorp.raft.backoff
public import Dsverify.Spec.github_com.hashicorp.raft.min
public import Dsverify.Spec.github_com.hashicorp.raft.max
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.After

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

theorem github_com.hashicorp.raft.Raft.replicateTo.wp_proof
    (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG))
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_setupAppendEntries : github_com.hashicorp.raft.Raft.setupAppendEntries.spec (GF := GF) (hG := hG))
    (wp_sendLatestSnapshot : github_com.hashicorp.raft.Raft.sendLatestSnapshot.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_appendStats : github_com.hashicorp.raft.appendStats.spec (GF := GF) (hG := hG))
    (wp_handleStaleTerm : github_com.hashicorp.raft.Raft.handleStaleTerm.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG))
    (wp_updateLastAppended : github_com.hashicorp.raft.updateLastAppended.spec (GF := GF) (hG := hG))
    (wp_backoff : github_com.hashicorp.raft.backoff.spec (GF := GF) (hG := hG))
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG))
    (wp_max : github_com.hashicorp.raft.max.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.replicateTo.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s γs lastIndex tid => by
  wp_start as ⟨#Hr, #Hs, #Hl, #Hlb, #Hstop, Hf, Htok⟩
  ihave #Hcell := replShared_nextCell r γ rc i T j s $$ Hs
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  wp_auto
  icases replFields_elim s $$ Hf with ⟨%fv, %ap, %nv, Hfl, Hap, Hn⟩
  ihave HI : iprop(∃ (rq : AppendEntriesRequest) (rp : AppendEntriesResponse) (st : time.Time)
      (pr : Server) (nv fv : w64) (ap : Bool),
      "req" ∷ req_ptr ↦ rq ∗ "resp" ∷ resp_ptr ↦ rp ∗ "start" ∷ start_ptr ↦ st ∗
      "peer" ∷ peer_ptr ↦ pr ∗ "Hn" ∷ s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} nv ∗
      "Hfl" ∷ s.[followerReplication, go!"failures"] ↦ fv ∗
      "Hap" ∷ s.[followerReplication, go!"allowPipeline"] ↦ ap) $$ [req resp start peer Hn Hfl Hap]
  · iexists _, _, _, _, _, _, _; iframe
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sdc, #Hsdc, %γsd, #Hsdbag⟩
  wp_for HI
  wp_join iprop(s_ptr ↦ s ∗ r_ptr ↦ r ∗ s.[followerReplication, go!"failures"] ↦ fv) with [Hfl s r]
  · wp_apply wp_backoff as %d -
    wp_apply +noauto (time.After.spec_pkgInit wp_After d)
    iintro %ach %γa #Hach
    wp_auto_lc 4
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hach
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hach
      inext
      iintro %t -
      wp_auto
      wp_join_done
    iapply BigAndL.bigAndL_singleton.2
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdc, γsd
    isplitr; · ipureintro; rfl
    isplitr; · iapply is_bag_is_chan $$ Hsdbag
    iapply bag_recv_au $$ [$Hlc3 $Hlc4] Hsdbag
    inext
    iintro %t Hf
    iexfalso; iexact Hf
  iintro ⟨s, r, Hfl⟩
  wp_auto_lc 1
  ihave ⟨#HcurT, ⟨%psf, #Hpeer⟩, #Hvj, #Hpl, -⟩ := replShared_core r γ i T j s $$ Hs
  unfold rwLock
  icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
  imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
  wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP] as Hown
  imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
  wp_apply (wp_loadUint64_own wp_LoadUint64 _ nv (DFrac.own (1 : Qp).half)) $$ [Hn] as Hn
  · iframe
  wp_apply wp_setupAppendEntries $$ [$Hr $Hs $Hl $Hlb $req $Htok] as %err ⟨Htok, %rq', req, Hres⟩
  ihave ⟨%e0, #He0⟩ := isRaftErr_of_init (GF := GF) .logNotFound $$ Hpkg
  ihave #Hg0 := isRaftErr_global .logNotFound e0 $$ He0
  ihave ⟨%x0, %Hx0⟩ := isRaftErr_ptr .logNotFound e0 $$ He0
  subst Hx0
  simp only [RaftErr.var] at *
  icases Hres with (⟨%Herr, %c, #Hce⟩ | ⟨%Herr, %prev, %pt, %ents, %lci, #Hbody, #Hvalid⟩)
  · -- setupAppendEntries failed: no request is sent
    ihave ⟨%x, %Hx⟩ := isRaftErr_ptr c err $$ Hce
    subst Hx
    wp_auto
    wp_if_destruct
    · ihave Hf := replFields_intro s fv ap nv $$ [Hfl Hap Hn]
      · iframe
      wp_apply wp_sendLatestSnapshot $$ [$Hr $Hs $Hl $Hlb $Hf $Htok] as %b %err2 ⟨Htok, Hf⟩
      wp_if_destruct
      rotate_left
      · -- stop
        wp_for_post
        iapply HΦ
        iframe
      cases err2 with
      | ok e2 =>
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
      | nil =>
      -- the snapshot was sent (or the RPC failed): poll the stop channel, loop if more to send
      icases replFields_elim s $$ Hf with ⟨%fv', %ap', %nv', Hfl, Hap, Hn⟩
      wp_auto_lc 1
      unfold replStopCh
      icases Hstop with ⟨%stc, #Hstc, #Hstopc⟩
      wp_auto
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_singleton.2
        simp only [chan.nonblockingClausePre]
        iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs.ch
        isplitr; · ipureintro; rfl
        isplitr
        · unfold stopChan
          icases Hstopc with ⟨#Hc, -⟩
          iexact Hc
        unfold nonblockingRecvAu
        isplit
        · iapply stopChan_nb_rcv_au $$ Hstopc Hlc1
          inext
          iintro %v %_ok
          wp_auto
          wp_for_post
          iapply HΦ
          iframe Htok
          iapply replFields_intro; iframe
        · itrivial
      wp_auto
      wp_apply (wp_loadUint64_own wp_LoadUint64 _ nv' (DFrac.own (1 : Qp).half)) $$ [Hn] as Hn
      · iframe
      wp_if_destruct
      · wp_for_post
        iframe
        iexists _, _, _, _, _, _, _
        iframe
      · wp_for_post
        iapply HΦ
        iframe Htok
        iapply replFields_intro; iframe
    · wp_for_post
      iapply HΦ
      iframe Htok
      iapply replFields_intro; iframe
  -- the request was built; the term check (the fork's fix)
  subst Herr
  wp_auto
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  icases Hvalid with (#Hvalid | #Hstale)
  rotate_left
  · wp_apply wp_getCurrentTerm.2 $$ [$Htc $Hstale] as %t ⟨#Hlbt, %Ht⟩
    wp_if_destruct
    · exfalso
      have h1 : uint.nat (W64 (T : Int)) ≤ T := by word
      omega
    · wp_for_post
      iapply HΦ
      iframe Htok
      iapply replFields_intro; iframe
  -- every read was of term `T`: the request is valid
  wp_apply wp_getCurrentTerm.2 $$ [$Htc $Hlb] as %t ⟨#Hlbt, %Ht⟩
  wp_if_destruct
  rotate_left
  · -- the term moved on: stop
    wp_for_post
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe
  have hT : T < 2 ^ 64 := by
    have h1 : uint.nat (W64 (T : Int)) ≤ T := by word
    have h2 : uint.nat (W64 (T : Int)) < 2 ^ 64 := by word
    omega
  ihave Hds : iprop([∗list] p ∈ ([] : List (SID × Nat)), durLb (GF := GF) γ p.1 p.2) $$ []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ihave HS : iprop([∗list] s0 ∈ ([] : List Snap), histLb (GF := GF) γ s0) $$ []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  imod histLb_now γ ⊤ (by solve_ndisj) [] [] (by simp) $$ [HInv HS Hds] with ⟨%ss, #Hss, -⟩
  · iframe #; iframe
  ihave #Haer := aeReq_intro γ rq' i T prev pt ents lci ss hT $$ [$Hbody $Hvalid $Hss]
  wp_apply wp_Now as %st' -
  ihave ⟨%x, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport
  icases Htr with ⟨-, -, -, -, -, -, -, #HAE, -⟩
  wp_auto
  wp_bind (App (App (App (App (Val #(methods x.ty _ x.v)) _) _) _) _)
  iapply HAE $$ Hvj req Haer resp Htok
  iintro %err req Htok Hres
  icases Hres with (⟨%Herr, %rp1, resp, #Hresp⟩ | ⟨#Herro, %rp1, resp⟩)
  rotate_left
  · -- the RPC failed
    ihave %Herr := errOk_ne_nil err $$ Herro
    cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe
  subst Herr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, -, -, -, ⟨%nlt, #Hnlt⟩, -⟩
  wp_auto
  wp_apply wp_appendStats
  wp_if_destruct
  · -- the follower has a newer term
    wp_apply wp_handleStaleTerm $$ [$Hr $Hs]
    wp_for_post
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe
  wp_apply wp_setLastContact $$ [$Hs]
  rcases rp1 with ⟨hdr1, tm1, ll1, succ1, nrb1⟩
  dsimp only
  wp_join iprop(∃ (nv' fv' : w64) (ap' : Bool), s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} nv' ∗
      s.[followerReplication, go!"failures"] ↦ fv' ∗ s.[followerReplication, go!"allowPipeline"] ↦ ap' ∗
      s_ptr ↦ s ∗ req_ptr ↦ rq' ∗ resp_ptr ↦ AppendEntriesResponse.mk hdr1 tm1 ll1 succ1 nrb1) with [Hn Hfl Hap s req resp]
  · -- failure: back off `nextIndex`
    wp_apply wp_min
    wp_apply wp_max
    wp_apply (wp_storeUint64_cell wp_StoreUint64 s nv _) $$ [Hn] as Hn
    · iframe; iframe #
    dsimp only
    wp_if_destruct
    · wp_join_done
      try (iexists _, _, _; iframe)
    · wp_join_done
      try (iexists _, _, _; iframe)
  · -- success: the follower acknowledged the request's entries
    unfold aeResp
    icases Hresp with ⟨-, (%Hf | ⟨(%Hhb | #Hack), -⟩), -⟩
    · exfalso; cases Hf
    · wp_apply (wp_updateLastAppended r γ rc i T j s _ rq' i prev pt ents lci) $$ [$Hs Hn $req $Hbody] as ⟨Hn, req⟩
      · iframe; unfold nextHalf; isplitl [Hn]; · iexists _; iframe
        ileft; ipureintro; exact Hhb.2.1
      iunfold nextHalf at Hn
      icases Hn with ⟨%nv', Hn⟩
      wp_join_done
      try (iexists _, _, _; iframe)
    wp_apply (wp_updateLastAppended r γ rc i T j s _ rq' i prev pt ents lci) $$ [$Hs Hn $req $Hbody] as ⟨Hn, req⟩
    · iframe; unfold nextHalf; isplitl [Hn]; · iexists _; iframe
      iright; iexact Hack
    iunfold nextHalf at Hn
    icases Hn with ⟨%nv', Hn⟩
    wp_join_done
    try (iexists _, _, _; iframe)
  iintro ⟨%nv', %fv', %ap', Hn, Hfl, Hap, s, req, resp⟩
  wp_auto_lc 1
  unfold replStopCh
  icases Hstop with ⟨%stc, #Hstc, #Hstopc⟩
  wp_auto
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs.ch
    isplitr; · ipureintro; rfl
    isplitr
    · unfold stopChan
      icases Hstopc with ⟨#Hc, -⟩
      iexact Hc
    unfold nonblockingRecvAu
    isplit
    · iapply stopChan_nb_rcv_au $$ Hstopc Hlc1
      inext
      iintro %v %_ok
      wp_auto
      wp_for_post
      iapply HΦ
      iframe Htok
      iapply replFields_intro; iframe
    · itrivial
  wp_auto
  wp_apply (wp_loadUint64_own wp_LoadUint64 _ nv' (DFrac.own (1 : Qp).half)) $$ [Hn] as Hn
  · iframe
  wp_if_destruct
  · wp_for_post
    iframe
    iexists _, _, _, _, _, _, _
    iframe
  · wp_for_post
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe

end proof

end Perennial
