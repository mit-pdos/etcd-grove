/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/newRaftNode.lean`. Lean-first (no Rocq
counterpart). Its one translated callee with a spec is `time.Now` (Perennial's linked result,
used directly, as `raftNode.tick`'s proof does); the rest are the contracts the spec takes
(`InvNodeStart.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newRaftNode
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `rnApP` depends on the names through `cum`, (D19i part 1) the storage and the start log, and
(D22 S-b) the node's names (`rnRtOk`) only. -/
theorem rnApP_cum (E : RNEnv GF) (γ1 γ2 : RNNames) (h : γ1.cum = γ2.cum)
    (hms : γ1.ms = γ2.ms) (hγs : γ1.γs = γ2.γs) (hpre : γ1.pre = γ2.pre)
    (hn : γ1.node = γ2.node) (hnl : γ1.nl = γ2.nl) :
    rnApP E γ1 = rnApP E γ2 := by
  unfold rnApP rnApN rnApSnap rnApR rnApGive rnHands rnCfgAt rnRtOk RNNames.srv
  rw [h, hms, hγs, hpre, hn, hnl]

set_option maxHeartbeats 0 in
theorem newRaftNode.wp_proof :
    newRaftNode.spec (GF := GF) (hG := hG) := by
  intro E node id nl pre ms γs cv Hlg Hhb
  wp_start as ⟨#Hzap, #Hsetlg, #Htdok, #Htkok⟩
  iunfold rnLoggerZapOk at Hzap
  iunfold rnSetLoggerOk at Hsetlg
  iunfold rnTimeoutDetectorOk at Htdok
  iunfold rnTickerOk at Htkok
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  (try wp_auto)
  -- `cfg.lg != nil`: `lg = NewRaftLoggerZap(cfg.lg)` (the `else` branch is dead)
  rw [show (decide (cv.lg' = null) = false) from decide_eq_false Hlg]
  (try wp_auto)
  wp_apply Hzap $$ %cv.lg' [] as %l -
  · ipureintro; exact Hlg
  (try wp_auto)
  -- `raft.SetLogger(lg)`
  wp_apply Hsetlg $$ %l []
  (try wp_auto)
  -- the struct's components: `new(sync.RWMutex)`, `time.Now()`, the detector, the channels
  wp_apply time.wp_Now as %t -
  (try wp_auto)
  wp_apply Htdok $$ %_ [] as %td #Htdi
  (try wp_auto)
  wp_apply chan.wp_make2 (V := ReadState) (W64 1) as %rsc %γrs ⟨#Hrsc, %Hrscap, Hrso⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply chan.wp_make2 (V := Loc) _ as %msc %γms ⟨#Hmsc, %Hmscap, Hmso⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply chan.wp_make1 (V := toApply) as %apc %γap ⟨#Hapc, %Hapcap, Hapo⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %stc %γst ⟨#Hstc, %Hstcap, Hsto⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %dnc %γd ⟨#Hdnc, %Hdncap, Hdno⟩
  (try wp_auto)
  -- the ghost state of the channels: `readStateC`'s bag of answered read states, `msgSnapC`'s
  -- bag of messages, `stopped`'s empty bag, `done`'s broadcast, `applyc`'s SPSC channel over
  -- `cum` at `[[]]`
  imod start_bag (V := ReadState) (srvReadStateOk E.γr.raft E.RQ) _ rsc γrs (by simp)
    $$ Hrsc Hrso with #Hrsb
  imod start_bag (V := Loc) rnSnapMsg _
    msc γms (by simp) $$ Hmsc Hmso with #Hmsb
  imod start_bag (V := Unit) (fun _ => E.ST) _ stc γst (by trivial) $$ Hstc Hsto with #Hstb
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γd dnc $$ Hdnc Hdno with Hdc
  icases ownBroadcastChan_open _ _ _ _ $$ Hdc with ⟨%γdi, #Hdint, Hdtok⟩
  ihave #HdcU : ownBroadcastChan (GF := GF) dnc γd iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdi; iframe #
  ihave Hdc := ownBroadcastChan_close _ _ _ .Pending γdi $$ [$Hdint $Hdtok]
  imod mono_list_own_alloc [([] : List EntryModel)] with ⟨%cum, Hcum, #Hlb⟩
  ihave #Hcum0 := monoListIdxOwn_get (γ := cum) 0 ([] : List EntryModel) (by simp) $$ Hlb
  imod start_spsc (V := toApply) apc
    (rnApP E ⟨node, id, nl, pre, ms, γs, ⟨γap, cum, cum⟩, cum, γd⟩)
    (fun _ => iprop(False)) γap $$ Hapc [Hapo] with ⟨%γsp, #Hspsc, Hprod, Hcons⟩
  · ileft; iexact Hapo
  -- the struct `r`
  (try wp_auto)
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hr0nn⟩
  iStructNamedSuffix «$r0» "R"
  (try wp_auto)
  -- `r.heartbeat != 0`: the ticker
  rw [show (decide (cv.heartbeat' = W64 0) = false) from decide_eq_false Hhb]
  (try wp_auto)
  wp_apply Htkok $$ %cv.heartbeat' [] as %tk #Htki
  · ipureintro; exact Hhb
  (try wp_auto)
  iapply HΦ
  iexists ⟨node, id, nl, pre, ms, γs, γsp, cum, γd⟩
  isplitr
  · ipureintro; simp
  iunfold rnBuilt
  iexists ⟨cv.lg', «$v1_ptr», t, cv, msc, apc, rsc, tk, td, stc, dnc⟩
  simp only [named]
  isplitl [lgR tickMuR latestTickTsR raftNodeConfigR msgSnapCR applycR readStateCR tickerR tdR
    stoppedR doneR]
  · iapply typedPointsto_combine _ _ _ Hr0nn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iframe «$v1» Hprod Hcons Hcum Hcum0 Hdc
  isplitr
  · ipureintro; simp
  iunfold rnParts
  simp only [named]
  iframe Htki Htdi HdcU
  isplitr
  · ipureintro; exact Hlg
  isplitr
  · iunfold isRNMsgSnapC; iexists γms; iexact Hmsb
  isplitr
  · iunfold isRNApplyc
    rw [rnApP_cum E ⟨node, id, nl, pre, ms, γs, γsp, cum, γd⟩
      ⟨node, id, nl, pre, ms, γs, ⟨γap, cum, cum⟩, cum, γd⟩ rfl rfl rfl rfl rfl rfl]
    iexact Hspsc
  isplitr
  · iunfold isRNReadStateC; iunfold isReadStateC; iexists γrs; iexact Hrsb
  iunfold rnStopBag; iexists γst; iexact Hstb

end proof

end EtcdGrove
end Perennial
