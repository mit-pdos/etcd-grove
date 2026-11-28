/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__heartbeat.lean (241f27e).
-/
/-
The proof of `Raft__heartbeat` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__heartbeat
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.cappedExponentialBackoff
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__LastContact
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.verifyFuture__vote
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
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

theorem github_com.hashicorp.raft.Raft.heartbeat.wp_proof
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG))
    (wp_cappedExponentialBackoff : github_com.hashicorp.raft.cappedExponentialBackoff.spec (GF := GF) (hG := hG))
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG))
    (wp_LastContact : github_com.hashicorp.raft.followerReplication.LastContact.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG))
    (wp_vote : github_com.hashicorp.raft.verifyFuture.vote.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.heartbeat.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s stopCh γh tid => by
  wp_start as ⟨#Hr, #Hs, #Hl, #Hlb, #Hstop, Hcons, Htok⟩
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  imod termLb_bound r γ i T $$ [$Htc $Hlb] with %hT
  ihave ⟨#HcurT, ⟨%psf, #Hpeer⟩, #Hvj, #Hpl, -, -, ⟨%nch, #Hnch, #Hnchb⟩, -⟩ := replShared_core r γ i T j s $$ Hs
  ihave ⟨%vch, #Hvch, #Hnl⟩ := replShared_notify r γ rc i T j s $$ Hs
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  ihave ⟨%x, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #Hid, #Haddr, -, ⟨%nlt, #Hnlt⟩, -⟩
  wp_auto
  wp_apply wp_getRPCHeader $$ [$Hr] as %h #Hh
  unfold isTransport
  icases Htr with ⟨-, -, -, #HEnc, -, -, -, #HAE, -⟩
  wp_bind (App (App (Val #(methods x.ty _ x.v)) _) _)
  iapply HEnc
  iintro %lsl Hlsl
  ipersist Hlsl
  wp_auto
  -- the heartbeat request is valid
  ihave #Hbody : aeBody (AppendEntriesRequest.mk h (W64 T) lsl 0 0 slice.nil 0) i T 0 0 [] 0 $$ []
  · unfold aeBody entPtrs
    iframe #
    isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iexists []
    isplitr; · iapply ownSlice_nil
    isplitr; · ipureintro; rfl
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  ihave #Hvalid := aeValid_heartbeat γ T i $$ Hl
  ihave HI : iprop(∃ (fv : w64) (rp : AppendEntriesResponse),
      "failures" ∷ failures_ptr ↦ fv ∗ "resp" ∷ resp_ptr ↦ rp ∗ "Hcons" ∷ spscConsumer γh ([] : List Unit))
      $$ [failures resp Hcons]
  · iexists _, _; iframe
  wp_for HI
  -- wait for a notification, the timeout, or the stop channel's close
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ spscConsumer γh ([] : List Unit) ∗
      r_ptr ↦ r ∗ stopCh_ptr ↦ stopCh) ∨ ⌜v = returnVal #()⌝)) at next with [Hcons r stopCh]
  · wp_apply (lc := 2) wp_config $$ [$Hr] as %c %Hc
    wp_apply wp_randomTimeout as %tch Htch
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      ihave ⟨%γn, #Hnb⟩ := notifyChan_bag nch $$ Hnchb
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nch, γn
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hnb
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hnb
      inext
      iintro %u -
      wp_auto
      ileft; iframe; ipureintro; rfl
    iapply BigAndL.bigAndL_cons.2
    isplit
    · icases Htch with (%Hnil | ⟨%γt, #Htb⟩)
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
        ileft; iframe; ipureintro; rfl
    iapply BigAndL.bigAndL_singleton.2
    ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stopCh, γh.chanName
    isplitr; · ipureintro; rfl
    unfold hbStop
    isplitr
    · unfold isSpsc; icases Hstop with ⟨#Hc, -⟩; iexact Hc
    iapply spsc_rcv_au $$ Hstop [$Hlc1 $Hlc2] Hcons
    inext
    iintro %u %ok Hok
    cases ok
    · wp_auto
      iright; ipureintro; rfl
    · simp only [↓reduceIte]
      icases Hok with ⟨Hf, -⟩
      iexfalso; iexact Hf
  iintro HQ
  icases HQ with (⟨%Hv, Hcons, r, stopCh⟩ | %Hv)
  rotate_left
  · subst Hv
    wp_auto
    wp_for_post
    iapply HΦ $$ Htok
  subst Hv
  wp_auto_lc 1
  unfold rwLock
  icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
  imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
  wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP] as Hown
  imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
  -- the pending verify futures: those registered before this heartbeat is sent
  wp_apply sync.Mutex.wp_Lock $$ [$Hnl] as ⟨Hlocked, Hinv⟩
  iunfold notifyInv at Hinv
  icases Hinv with ⟨%m, %M, Hn, Hm, HM⟩
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType verifyFuture.ty)
    (go.GoType.StructType [])) as %m2 Hm2
  wp_apply sync.Mutex.wp_Unlock $$ [$Hnl $Hlocked Hn Hm2]
  · inext
    unfold notifyInv
    iexists m2, ∅
    iframe
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    iempintro
  -- the heartbeat's snapshot, after every pending registration
  imod notify_snap ⊤ (by solve_ndisj) γ rc i T vch j M $$ [HInv HM] with ⟨%ss, #Hss, HP⟩
  · iframe #; iframe
  ihave #Haer := aeReq_intro γ _ i T 0 0 [] 0 ss hT $$ [$Hbody $Hvalid $Hss]
  wp_bind (App (App (App (App (Val #(methods x.ty _ x.v)) _) _) _) _)
  iapply HAE $$ Hvj req Haer resp Htok
  iintro %err req Htok Hres
  icases Hres with (⟨%Herr, %rp1, resp, #Hresp⟩ | ⟨#Herro, %rp1, resp⟩)
  rotate_left
  · -- the heartbeat failed: the pending futures go back to the notify set
    ihave %Herr := errOk_ne_nil err $$ Herro
    cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hnl] as ⟨Hlocked, Hinv⟩
    iunfold notifyInv at Hinv
    icases Hinv with ⟨%m', %M', Hn, Hm', HM'⟩
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range_gen (K := Loc) (V := Unit) (fun keys (idx : Nat) mm => iprop(⌜mm = M⌝ ∗
        ∃ (N : GMap Loc Unit) (x : Loc), s_ptr ↦ s ∗ v_ptr ↦ x ∗
        s.[followerReplication, go!"notify"] ↦ m' ∗ m' ↦$ N ∗
        ([∗map] w ↦ _u ∈ N, notifyEntry γ rc i T vch j w) ∗
        [∗list] k ∈ keys.drop idx, pendEntry γ rc i T vch j ss k))) $$ Hm
    iintro %keys %hkeys
    obtain ⟨hkm, hksz, hknd⟩ := hkeys
    isplitl [s v Hn Hm' HM' HP]
    · isplitr; · ipureintro; rfl
      iexists M', _
      iframe
      simp only [List.drop_zero]
      iapply bigSepM_keys_loc _ keys M hknd hkm $$ HP
    isplitl []
    · imodintro
      iintro %idx %key %u %mm ⟨%hk1, %hk2⟩ ⟨%hm, %N, %x, s, v, Hn, Hm', HN, Hl⟩ Hm
      subst mm
      have hjl : idx < keys.length := (List.getElem?_eq_some_iff.mp hk1).1
      rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hk1).2]
      ihave ⟨Hk, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
      wp_auto
      wp_apply (wp_mapInsert (K := Loc) (V := Unit) (go.GoType.PointerType verifyFuture.ty) m' N key ())
        $$ [$Hm'] as Hm'
      unfold forMapPostcondition
      iright; ileft
      isplitr; · ipureintro; rfl
      iexists M
      iframe Hm
      isplitr; · ipureintro; rfl
      iexists _, key
      iframe
      iapply BigSepM.bigSepM_insert_elim (Φ := fun w (_ : Unit) => notifyEntry γ rc i T vch j w)
        $$ [Hk] HN
      iapply pendEntry_notify $$ Hk
    isplitl []
    · imodintro
      iintro %idx %key %mm ⟨%hk1, %hk2⟩ ⟨%hm, -⟩
      subst mm
      exact absurd ((hkm key).mp (List.mem_of_getElem? hk1)) (by rw [hk2]; simp)
    iintro %mm ⟨%hm, %N, %x, s, v, Hn, Hm', HN, -⟩ Hm
    subst mm
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hnl $Hlocked Hn Hm' HN]
    · inext
      unfold notifyInv
      iexists m', N
      iframe
    wp_apply wp_config $$ [$Hr] as %c %Hc
    wp_apply wp_cappedExponentialBackoff as %d -
    wp_apply (wp_LastContact r γ rc i T j s tid) $$ [$Hs $Htok] as %t Htok
    wp_apply (wp_observe r γ rc i (SState.mk 0 [] 0 [] (0, 0) 0) _ tid) $$ [$Hr $Htok] as ⟨-, Htok⟩
    · iapply obsArg_named; exact failedHb_ne
    ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
    · iPkgInit
    wp_apply +noauto time.After.spec_pkgInit wp_After _ $$ [$Htime]
    iintro %ach %γa #Hach
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hach
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hach
      inext
      iintro %u -
      wp_auto
      wp_for_post
      iframe
      iexists _, _; iframe
    iapply BigAndL.bigAndL_singleton.2
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stopCh, γh.chanName
    isplitr; · ipureintro; rfl
    unfold hbStop
    isplitr
    · unfold isSpsc; icases Hstop with ⟨#Hc, -⟩; iexact Hc
    iapply spsc_rcv_au $$ Hstop [$Hlc1 $Hlc2] Hcons
    inext
    iintro %u %ok Hok
    cases ok
    · wp_auto
      wp_for_post
      iapply HΦ $$ Htok
    · simp only [↓reduceIte]
      icases Hok with ⟨Hf, -⟩
      iexfalso; iexact Hf
  subst Herr
  wp_auto
  wp_join with [Htok r peer]
  · wp_apply (wp_observe r γ rc i (SState.mk 0 [] 0 [] (0, 0) 0) _ tid) $$ [$Hr $Htok] as ⟨-, Htok⟩
    · iapply obsArg_named; exact resumedHb_ne
    wp_join_done
  wp_apply wp_setLastContact $$ [$Hs]
  -- the votes: each pending future gets the response (a success carries `j`'s witness after `ss`)
  ihave #Hsw : iprop(⌜rp1.Success' = false⌝ ∨ respWit γ j T ss) $$ [Hresp]
  · unfold aeResp
    icases Hresp with ⟨-, (%Hf | ⟨-, #Hw⟩), -⟩
    · ileft; ipureintro; exact Hf
    · iright; iexact Hw
  wp_join iprop(True) at next
  · cases nlt <;> (wp_auto; wp_join_done; try itrivial)
  iintro -
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_gen (K := Loc) (V := Unit) (fun keys (idx : Nat) mm => iprop(⌜mm = M⌝ ∗
      ∃ x : Loc, v_ptr ↦ x ∗ resp_ptr ↦ rp1 ∗
      [∗list] k ∈ keys.drop idx, pendEntry γ rc i T vch j ss k))) $$ Hm
  iintro %keys %hkeys
  obtain ⟨hkm, hksz, hknd⟩ := hkeys
  isplitl [v resp HP]
  · isplitr; · ipureintro; rfl
    iexists _
    iframe
    simp only [List.drop_zero]
    iapply bigSepM_keys_loc _ keys M hknd hkm $$ HP
  isplitl []
  · imodintro
    iintro %idx %key %u %mm ⟨%hk1, %hk2⟩ ⟨%hm, %x, v, resp, Hl⟩ Hm
    subst mm
    have hjl : idx < keys.length := (List.getElem?_eq_some_iff.mp hk1).1
    rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hk1).2]
    ihave ⟨Hk, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    iunfold pendEntry at Hk
    icases Hk with ⟨%sv, %L, #Hsv, %Hle, #Hreg, Hvt, %HjL⟩
    wp_auto
    wp_apply (wp_vote r γ rc i T sv L vch j key rp1.Success') $$ [Hvt]
    · iframe #
      icases Hsw with (%Hf | #Hw)
      · ileft; ipureintro; exact Hf
      · iright
        iframe
        iunfold respWit at Hw
        icases Hw with ⟨%sq, #Hsq, %Hsq⟩
        isplitl
        · unfold respWit
          iexists sq
          iframe #
          ipureintro; exact ⟨snapLe_trans Hle Hsq.1, Hsq.2⟩
        ipureintro; exact HjL
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists M
    iframe Hm
    isplitr; · ipureintro; rfl
    iexists key
    iframe
  isplitl []
  · imodintro
    iintro %idx %key %mm ⟨%hk1, %hk2⟩ ⟨%hm, -⟩
    subst mm
    exact absurd ((hkm key).mp (List.mem_of_getElem? hk1)) (by rw [hk2]; simp)
  iintro %mm ⟨%hm, %x, v, resp, -⟩ Hm
  subst mm
  wp_for_post
  iframe
  iexists _, _; iframe

end proof

end Perennial
