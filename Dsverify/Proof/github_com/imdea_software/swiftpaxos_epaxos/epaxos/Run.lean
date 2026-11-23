/-
`(*Replica).run`: connect to the peers (`ConnectToPeers`), fix the peer order
(`ComputeClosestPeers`), start the executor, the clocks and the client listener, then the event
loop: each event's critical section (`RunCalls.lean`) under the instance lock.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunClock

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- A deliverable message of kind `k`, opened. -/
theorem deliverChanP_open (γ : EpNames) (i : Nat) (k : MsgKind) (v : GoInterface) :
    deliverChanP (GF := GF) γ i k v ⊢ ∃ (d n : Nat) (m : Msg) (l : Loc),
      ⌜m.kind = some k ∧ v = interface.mkOk (go.GoType.PointerType k.ty) #l ∧ m.wf ∧ d < nR ∧
        d ≠ i⌝ ∗ ownMsg l m (DFrac.own 1) ∗ msgSent γ d i n m ∗ delivTok γ i d n := by
  unfold deliverChanP deliverable msgObj
  iintro ⟨%d, %n, %m, %hk, ⟨%hd, ⟨%k', %l, %hkl, Hm⟩, %hwf, #Hs, Ht⟩⟩
  have hkk : k' = k := by rw [hk] at hkl; exact (Option.some.inj hkl.1).symm
  subst hkk
  iexists d, n, m, l
  isplitr
  · ipureintro
    exact ⟨hk, hkl.2, hwf, by simpa [nRep, nR] using hd.1, hd.2⟩
  iframe
  iexact Hs

theorem fwRO_bchan (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwRO (GF := GF) γ r id L p ⊢ fld r go!"BeaconChan" ↦□ p.bchan ∗
      ∃ γc : ChanNames, isChanBag (V := Loc) γc p.bchan (fun _ => iprop(False)) := by
  rw [fwRO_unseal]; unfold fwRODef
  iintro #H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, Hf, -, -, -, -, -, -, -, -, -, -, -, Hb⟩
  iframe Hf Hb

theorem chans_open (Q : MsgKind → IProp GF) :
    ([∗list] k ∈ MsgKind.all, Q k) ⊢ Q .prepare ∗ Q .prepareReply ∗ Q .preAccept ∗
      Q .preAcceptReply ∗ Q .accept ∗ Q .acceptReply ∗ Q .commit ∗ Q .tryPreAccept ∗
      Q .tryPreAcceptReply := by
  unfold MsgKind.all
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H4, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H5, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H6, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H7, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H8, -⟩
  iframe

set_option maxHeartbeats 4000000 in
set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 1000 in
theorem wp_run (hCP : replica.Replica.ConnectToPeers.spec (GF := GF))
    (hCCP : replica.Replica.ComputeClosestPeers.spec (GF := GF))
    (hWC : replica.Replica.WaitForClientConnections.spec (GF := GF))
    (hP : dlog.Logger.Printf.spec (GF := GF)) (hS : CmdStringSpec (GF := GF)) (hH : HandlerSpecs (GF := GF))
    (hEx : ExecuteCommandsSpec (GF := GF))
    (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) :
    {{ runPre (GF := GF) γ i r rr L p }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"run")) (Val #()))
    {{ RET #(); False }} := by
  wp_start as Hpre
  unfold runPre
  icases Hpre with ⟨#Hpk, #Hisr, #Hrr, #Hro, #Hfz, Hst, #Hchans, ⟨%rch, %γr, #Hrf, #Hrbag⟩,
    ⟨%e, #He, #Her⟩, #Hbw, ⟨%sc0, Hscf⟩, ⟨%fc0, Hfcf⟩, Hcpc⟩
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hro
  ihave ⟨#HBeacon, #HDur⟩ := fwFrozen_fields _ _ _ _ $$ Hfz
  have hi : i < nR := by have := HLn.1; have := HLn.2; simp only [nRep, nR] at *; omega
  have hL : L.length = nR := by have := HLn.1; simp only [nRep, nR] at *; omega
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hCP γ rr i L p iprop(True)) $$ [$Hro $Hfz $Hst] as ⟨#Hfw, Hlis, Hpref⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hCCP γ rr i L p iprop(True)) $$ [$Hfw $Hpref] as %sl ⟨%ord, #Hpo⟩
  ihave #Hctx : hctx γ i r rr L p iprop(True) ord $$ []
  · unfold hctx; iframe #
  wp_apply wp_fork
  · wp_apply (hEx γ i r rr L p iprop(True) ord e rch γr) $$ [] as Hf
    · iframe #
    iexfalso; iexact Hf
  wp_apply (chan.wp_make2 (V := Bool) (W64 1)) as %sch %γs ⟨#Hsch, -, Hso⟩
  · ipureintro; decide
  iapply fupd_wp
  imod (start_bag (V := Bool) (fun _ => iprop(True)) (ChanState.Buffered []) sch γs trivial)
    $$ Hsch Hso with #Hsbag
  imodintro
  wp_apply (chan.wp_make2 (V := Bool) (W64 1)) as %fch %γf ⟨#Hfch, -, Hfo⟩
  · ipureintro; decide
  iapply fupd_wp
  imod (start_bag (V := Bool) (fun _ => iprop(True)) (ChanState.Buffered []) fch γf trivial)
    $$ Hfch Hfo with #Hfbag
  imodintro
  ipersist Hscf
  ipersist Hfcf
  ihave #Hfast : clockFld r go!"fastClockChan" fch $$ []
  · unfold clockFld epaxosClockChanOk; iframe Hfcf; iright; iexists γf; iexact Hfbag
  ihave #Hslow : clockFld r go!"slowClockChan" sch $$ []
  · unfold clockFld epaxosClockChanOk; iframe Hscf; iright; iexists γs; iexact Hsbag
  iclear Hfcf Hscf
  wp_apply wp_fork
  · wp_apply (wp_slowClock r rr sch) $$ [] as Hf
    · iframe #
    iexfalso; iexact Hf
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_fork $$ [Hlis]
  · wp_method_call
    wp_call
    wp_auto
    wp_apply (hWC γ rr i L p iprop(True)) $$ [$Hfw $Hlis] as Hf
    iexfalso; iexact Hf
  -- the channels
  icases chans_open _ $$ Hchans with ⟨⟨%c0, %g0, #Hc0, #Hb0⟩, ⟨%c1, %g1, #Hc1, #Hb1⟩,
    ⟨%c2, %g2, #Hc2, #Hb2⟩, ⟨%c3, %g3, #Hc3, #Hb3⟩, ⟨%c4, %g4, #Hc4, #Hb4⟩, ⟨%c5, %g5, #Hc5, #Hb5⟩,
    ⟨%c6, %g6, #Hc6, #Hb6⟩, ⟨%c7, %g7, #Hc7, #Hb7⟩, ⟨%c8, %g8, #Hc8, #Hb8⟩⟩
  simp only [MsgKind.chanField]
  icases fwRO_proposeChan _ _ _ _ _ $$ Hro with ⟨%γp, #Hpbag⟩
  ihave #Hisr' := Hisr
  rw [isReplica_unseal]; unfold isReplicaDef
  icases Hisr' with ⟨%rr', %L', %p', -, -, -, -, ⟨%lp, #Hlp, #Hlock⟩, #Hinv, -⟩
  icases fwRO_bchan _ _ _ _ _ $$ Hro with ⟨#HBc, %γb, #Hbbag⟩
  wp_for
  wp_apply wp_loadClock $$ Hfast as #Hok1
  wp_apply (lc := 2) wp_loadClock $$ Hslow as #Hok12
  wp_apply_core chan.wp_select_blocking_nil
  -- `propose := <-onOffProposeChan` (`ProposeChan`: batching is off)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, p.pchan, γp
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hpbag
    iapply bag_recv_au γp p.pchan _ _ $$ [$Hlc1 $Hlc2] Hpbag
    inext
    iintro %g Hg
    wp_auto
    wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_proposeCall hH.propose γ i r rr L p iprop(True) ord g hi hL)
      $$ [$Hctx $Hls $Hg $Hcpc $Hlc1] as ⟨Hls, Hcpc⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_method_call
    wp_call
    wp_auto
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · unfold epaxosClockChanOk
    icases Hok1 with (%Hnil | ⟨%γk, #Hbk⟩)
    · iright
      iapply chan.nilClausePre_recv Bool _ _ (by rw [Hnil]; rfl)
    ileft
    simp only [chan.blockingClausePre]
    iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, fch, γk
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbk
    iapply bag_recv_au γk fch _ _ $$ [$Hlc1 $Hlc2] Hbk
    inext
    iintro %b -
    wp_auto
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c0, g0
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb0
    iapply bag_recv_au g0 c0 _ _ $$ [$Hlc1 $Hlc2] Hb0
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .prepare v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .prepare go!"handlePrepare" hH.prepare γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c2, g2
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb2
    iapply bag_recv_au g2 c2 _ _ $$ [$Hlc1 $Hlc2] Hb2
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .preAccept v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .preAccept go!"handlePreAccept" hH.preAccept γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c4, g4
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb4
    iapply bag_recv_au g4 c4 _ _ $$ [$Hlc1 $Hlc2] Hb4
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .accept v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .accept go!"handleAccept" hH.accept γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c6, g6
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb6
    iapply bag_recv_au g6 c6 _ _ $$ [$Hlc1 $Hlc2] Hb6
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .commit v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_commitCall hP hS γ i r rr L p iprop(True) ord l m d n hk hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c1, g1
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb1
    iapply bag_recv_au g1 c1 _ _ $$ [$Hlc1 $Hlc2] Hb1
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .prepareReply v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .prepareReply go!"handlePrepareReply" hH.prepareReply γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c3, g3
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb3
    iapply bag_recv_au g3 c3 _ _ $$ [$Hlc1 $Hlc2] Hb3
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .preAcceptReply v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .preAcceptReply go!"handlePreAcceptReply" hH.preAcceptReply γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c5, g5
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb5
    iapply bag_recv_au g5 c5 _ _ $$ [$Hlc1 $Hlc2] Hb5
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .acceptReply v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .acceptReply go!"handleAcceptReply" hH.acceptReply γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c7, g7
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb7
    iapply bag_recv_au g7 c7 _ _ $$ [$Hlc1 $Hlc2] Hb7
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .tryPreAccept v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .tryPreAccept go!"handleTryPreAccept" hH.tryPreAccept γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, c8, g8
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb8
    iapply bag_recv_au g8 c8 _ _ $$ [$Hlc1 $Hlc2] Hb8
    inext
    iintro %v Hv
    icases deliverChanP_open γ i .tryPreAcceptReply v $$ Hv with ⟨%d, %n, %m, %l, %Hm, Hm, #Hs, Ht⟩
    obtain ⟨hk, rfl, hwf, hd, hne⟩ := Hm
    simp only [MsgKind.ty]
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_deliverCall .tryPreAcceptReply go!"handleTryPreAcceptReply" hH.tryPreAcceptReply γ i r rr L p iprop(True) ord l m d n hk hwf hd hne hi hL)
      $$ [$Hctx $Hls $Hm $Hs $Ht $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, p.bchan, γb
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbbag
    iapply bag_recv_au γb p.bchan _ _ $$ [$Hlc1 $Hlc2] Hbbag
    inext
    iintro %b Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2
  isplit
  · unfold epaxosClockChanOk
    icases Hok12 with (%Hnil | ⟨%γk, #Hbk⟩)
    · iright
      iapply chan.nilClausePre_recv Bool _ _ (by rw [Hnil]; rfl)
    ileft
    simp only [chan.blockingClausePre]
    iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, sch, γk
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbk
    iapply bag_recv_au γk sch _ _ $$ [$Hlc1 $Hlc2] Hbk
    inext
    iintro %b -
    wp_auto
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, rch, γr
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hrbag
    iapply bag_recv_au γr rch _ _ $$ [$Hlc1 $Hlc2] Hrbag
    inext
    iintro %iid Hv
    unfold recoverReq
    icases Hv with ⟨%q, %k, %nb, Hiid, #Hlb, %Hqk⟩
    wp_auto
    wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
    unfold instLockInv
    icases HL with ⟨Hls, Hstack⟩
    wp_apply (wp_recoverCall hH.recover γ i r rr L p iprop(True) ord q k nb Hqk.1 Hqk.2 hi hL)
      $$ [$Hctx $Hls $Hlb $Hlc1 $Hlc2] as Hls
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hls $Hstack]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
