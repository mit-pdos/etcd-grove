/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__requestCurrentIndex.lean`.
Lean-first (no Rocq counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__requestCurrentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__sendReadIndex
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Info

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- The registrations of the request ids sent, with one more. -/
theorem read_reg_insert (RQ : w64 → w64 → IProp GF) (n : w64) (m : GMap w64 Unit) (rid : w64) :
    ⊢ (□ ∀ k, ⌜m !! k = some ()⌝ -∗ □ RQ k n) -∗ □ RQ rid n -∗
      □ ∀ k, ⌜(<[rid := ()]> m) !! k = some ()⌝ -∗ □ RQ k n := by
  iintro #Hreg #Hrq !> %k %hk
  by_cases hkr : k = rid
  · subst hkr; iexact Hrq
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkr)] at hk
    iapply Hreg $$ %k %hk

/-- No registration in the empty map. -/
theorem read_reg_empty (RQ : w64 → w64 → IProp GF) (n : w64) :
    ⊢ (□ ∀ k, ⌜(∅ : GMap w64 Unit) !! k = some ()⌝ -∗ □ RQ k n : IProp GF) := by
  iintro !> %k %hk
  simp at hk

set_option hygiene false in
/-- The deferred `retryTimer.Stop()` and `errorTimer.Stop()` at a return. -/
local macro "rci_defers" : tactic => `(tactic| (
  (try wp_auto)
  (try wp_for_post)
  wp_apply time.Timer.wp_Stop $$ [] as %_ -
  · ileft; iexists rtc, γrt; iexact Hrt
  (try wp_auto)
  wp_apply time.Timer.wp_Stop $$ [] as %_ -
  · ileft; iexists etc, γet; iexact Het
  (try wp_auto)))

set_option hygiene false in
/-- A return with the error variable `e` (`ErrLeaderChanged`, `ErrTimeout`, `ErrStopped`). -/
local macro "rci_ret_err" Ha:ident : tactic => `(tactic| (
  rci_defers
  iapply HΦ; iframe HLR $Ha:ident; iintro %h; cases h))

set_option hygiene false in
/-- A new request after `firstCommitInTermNotifier` or `retryTimer.C` (the first-commit channel
`fcN` in the invariant then): a new id, registered in `requestIDs`, `sendReadIndex`, a return on
its error, else `retryTimer.Reset` and `continue`. -/
local macro "rci_resend" fcN:term:max : tactic => `(tactic| (
  ihave HN1 := HNRu
  imod HN1
  (try wp_auto)
  wp_apply HNR $$ HN1 as %rid' -
  wp_apply wp_mapInsert go.uint64 mref _ rid' () $$ Hm as Hm
  wp_apply hSRI r γr RQ LR NR rid' n $$ [HLR] as %err' ⟨HLR, #HaE', HRQ'⟩
  · iframe #; iframe HLR
  cases err' with
  | ok ei' =>
    wp_auto
    rci_defers
    iapply HΦ; iframe HLR HaE'; iintro %h; cases h
  | nil =>
    ihave #HRQ'' := HRQ' $$ %rfl
    wp_auto
    wp_apply time.Timer.wp_Reset rt rtc γrt _ $$ [] as %_ -
    · iexact Hrt
    wp_for_post
    iframe
    iexists _, rid', $fcN
    iframe
    isplitl
    · iapply read_reg_insert RQ n m rid' $$ Hreg HRQ''
    simp only [named]
    first | iexact Hfc | iexact Hfcn))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem read.Read.requestCurrentIndex.wp_proof
    (hSRI : read.Read.sendReadIndex.spec (GF := GF) (hG := hG))
    (hZU : zap.Uint64.spec (GF := GF) (hG := hG))
    (hZD : zap.Duration.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hI : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    read.Read.requestCurrentIndex.spec (GF := GF) (hG := hG) := by
  intro r γr RQ LR NR lcn n
  wp_start as ⟨#Hpre, HLR, #HNRu, #Hlcn, #Hc⟩
  ihave #Hpre' := Hpre
  iunfold isReadLoopPre at Hpre'
  icases Hpre' with ⟨%srv, %rf, %wc, %γw, #Hsf, #Hsrv, #Hrf, #Hraft, -, -, -, -, -⟩
  iunfold isReadServer at Hsrv
  icases Hsrv with ⟨-, %si, %Hsi, #HStopping, -, #HFC, #HLg, -, -, #HNR, #HRT⟩
  iunfold isReadRaft at Hraft
  icases Hraft with ⟨%ri, %Hri, #HRS, -⟩
  subst Hsi Hri
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%cS, #HcS, #HcSs⟩, ⟨%cF, #HcF, #HcFs⟩, ⟨%dR, #HdR⟩, #HStop, #HLCh, #HTO, -,
    -, -⟩
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at HcSs HcFs
  icases HcSs with ⟨#HIncS, -⟩
  icases HcFs with ⟨#HIncF, -⟩
  ihave ⟨%eStop, #HeStop, #HaStop⟩ := errVarLeaf_get _ $$ HStop
  ihave ⟨%eLC, #HeLC, #HaLC⟩ := errVarLeaf_get _ $$ HLCh
  ihave ⟨%eTO, #HeTO, #HaTO⟩ := errVarLeaf_get _ $$ HTO
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hm
  ihave HN0 := HNRu
  imod HN0
  wp_apply HNR $$ [$HN0] as %rid0 -
  wp_apply wp_mapInsert go.uint64 mref _ rid0 () $$ [$Hm] as Hm
  wp_apply hSRI r γr RQ LR NR rid0 n $$ [HLR] as %err0 ⟨HLR, #HaE0, HRQ0⟩
  · iframe #; iframe HLR
  cases err0 with
  | ok ei0 =>
    wp_auto
    iapply HΦ
    iframe HLR HaE0
    iintro %h; cases h
  | nil =>
  ihave #HRQ0' := HRQ0 $$ %rfl
  wp_auto
  wp_apply HLg $$ [$HLR] as %lg ⟨%Hlg, HLR⟩
  wp_apply HRT as %d -
  wp_apply time.wp_NewTimer as %et %etc %γet #Het
  wp_apply time.wp_NewTimer as %rt %rtc %γrt #Hrt
  iunfold srvChanOkR at HFC
  wp_apply HFC $$ [$HLR] as %fc0 ⟨#Hfc0, HLR⟩
  ihave #Het' := Het
  iunfold time.isTimer at Het'
  icases Het' with ⟨#HetC, #HetB, -⟩
  ihave #Hrt' := Hrt
  iunfold time.isTimer at Hrt'
  icases Hrt' with ⟨#HrtC, #HrtB, -⟩
  ihave HI : iprop(∃ (m : GMap w64 Unit) (rid : w64) (fc : Loc),
      "requestID" ∷ requestID_ptr ↦ rid ∗
      "Hm" ∷ mref ↦$ m ∗
      "#Hreg" ∷ (□ ∀ k, ⌜m !! k = some ()⌝ -∗ □ RQ k n) ∗
      "firstCommitInTermNotifier" ∷ firstCommitInTermNotifier_ptr ↦ fc ∗
      "#Hfc" ∷ bcastChan fc iprop(True)) $$ [requestID Hm firstCommitInTermNotifier]
  · iexists _, rid0, fc0
    iframe
    isplitl
    · iapply read_reg_insert RQ n ∅ rid0 $$ [] HRQ0'
      iapply read_reg_empty
    · simp only [named]; iexact Hfc0
  wp_for HI
  wp_apply (lc := 2) HRS as %rsc #Hrsc
  iunfold srvChanOk at HStopping
  wp_apply HStopping as %stc #Hstc
  ihave #Hfcc := Hfc
  ihave #Hlcnc := Hlcn
  iunfold bcastChan at Hstc Hlcnc Hfcc
  icases Hstc with ⟨%γst, #Hstc⟩
  icases Hlcnc with ⟨%γlc, #Hlcn'⟩
  icases Hfcc with ⟨%γfc, #Hfc'⟩
  iunfold isReadStateC at Hrsc
  icases Hrsc with ⟨%γrs, #Hrsc⟩
  wp_apply_core chan.wp_select_blocking
  -- `rs := <-r.raft.ReadState()`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists go_etcd_io.raft.v3.ReadState, inferInstance, inferInstance, inferInstance, inferInstance,
      rsc, γrs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hrsc
    iapply bag_recv_au γrs rsc _ _ $$ [$Hlc1 $Hlc2] Hrsc
    inext
    iintro %rs #Hrs
    wp_auto
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.nonblockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, lcn, γlc
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hlcn'
        iapply blocking_rcv_implies_nonblocking
        iapply broadcast_chan_receive _ _ _ _ _ $$ Hlcn'
        iintro ⟨-, -⟩
        wp_auto
        wp_apply HIncF
        rci_ret_err HaLC
      · iapply BigAndL.bigAndL_nil.2; itrivial
    · wp_auto
      iunfold readStateOk at Hrs
      icases Hrs with ⟨%bs, #Hbs, %Hbl, #Hans⟩
      ihave %Hsl := ownSlice_len _ _ _ $$ Hbs
      wp_if_destruct
      rotate_left
      · exfalso; apply Hif; word
      wp_apply encoding.binary.wp_BigEndian_Uint64 rs.RequestCtx' bs DFrac.discard [] Hbl $$ [] as -
      · simp only [List.append_nil]; iexact Hbs
      wp_apply wp_map_lookup2 go.uint64 (go.StructType []) mref m (leToU64 bs.reverse) _ $$ [$Hm] as Hm
      cases hk : m !! leToU64 bs.reverse with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
        wp_auto
        wp_apply hZU as %f -
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %fs ⟨-, -⟩
        (try wp_auto)
        wp_apply hW lg _ _ $$ []
        · iframe #; ipureintro; exact Hlg
        (try wp_auto)
        wp_apply HIncS
        (try wp_auto)
        wp_for_post
        iframe
        iexists m, rid, fc
        iframe
        iframe #
      | some u =>
        simp only [Option.isSome_some, _root_.decide_true, Bool.not_true]
        wp_auto
        ihave #Hrq := Hreg $$ %(leToU64 bs.reverse) %hk
        ihave %Hle := Hans $$ %(leToU64 bs.reverse) %n %(beBytes_of_length bs Hbl) Hrq
        wp_for_post
        rci_defers
        iapply HΦ
        iframe HLR
        isplitr
        · iapply applyErrIs_nil
        iintro -; ipureintro; exact Hle
  -- `<-leaderChangedNotifier`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, lcn, γlc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hlcn'
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hlcn'
    iintro ⟨-, -⟩
    wp_auto
    wp_apply HIncF
    rci_ret_err HaLC
  -- `<-firstCommitInTermNotifier`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, fc, γfc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hfc'
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hfc'
    iintro ⟨-, -⟩
    wp_auto
    wp_apply HFC $$ [$HLR] as %fcn ⟨#Hfcn, HLR⟩
    (try wp_auto)
    wp_apply hI lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg
    rci_resend fcn
  -- `<-retryTimer.C`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance,
      rtc, γrt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HrtB
    iapply bag_recv_au γrt rtc _ _ $$ [$Hlc1 $Hlc2] HrtB
    inext
    iintro %tm -
    wp_auto
    wp_apply hZU as %f1 -
    wp_apply hZD as %f2 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    (try wp_auto)
    wp_apply hW lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg
    rci_resend fc
  -- `<-errorTimer.C`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance,
      etc, γet
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HetB
    iapply bag_recv_au γet etc _ _ $$ [$Hlc1 $Hlc2] HetB
    inext
    iintro %tm -
    wp_auto
    wp_apply HRT as %d' -
    wp_apply hZD as %f2 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    (try wp_auto)
    wp_apply hW lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg
    (try wp_auto)
    wp_apply HIncS
    rci_ret_err HaTO
  -- `<-r.server.Stopping()`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstc
    iintro ⟨-, -⟩
    wp_auto
    rci_ret_err HaStop
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
