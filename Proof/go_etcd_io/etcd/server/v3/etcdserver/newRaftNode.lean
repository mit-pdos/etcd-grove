/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/newRaftNode.lean`. Lean-first (no Rocq
counterpart). Its translated callees with specs are `time.Now` (Perennial's linked result,
used directly, as `raftNode.tick`'s proof does) and (2026-11-03, until then the contract
`rnTickerOk` in the spec's precondition) `time.NewTicker` and the ticker's `Stop`, Perennial's
proved specs, taken as callee specs (`isRNTicker_of_time`; linked to Perennial's results,
`etc/link-lean-first-server.txt`): `time.Now` predates the layout's callee-spec convention and is
left as it was; the rest are the contracts the spec takes (`InvNodeStart.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newRaftNode
public import Perennial.Proof.time
public import Perennial.Spec.time.NewTicker

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
    (_hms : γ1.ms = γ2.ms) (hγs : γ1.γs = γ2.γs) (hpre : γ1.pre = γ2.pre)
    (hn : γ1.node = γ2.node) (hnl : γ1.nl = γ2.nl) (hid : γ1.id = γ2.id) (hkey : γ1.key = γ2.key)
    (hwal : γ1.wal = γ2.wal) (ha : γ1.a0 = γ2.a0) :
    rnApP E γ1 = rnApP E γ2 := by
  unfold rnApP rnApN rnApSnap rnApR rnApGive rnHands rnView rnGhost rnRtOk rnLogOf RNNames.srv
    rnWalHanded
  rw [h, hγs, hpre, hn, hnl, hid, hkey, hwal, ha]

set_option maxHeartbeats 0 in
theorem newRaftNode.wp_proof
    (wp_NewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (wp_TStop : time.Ticker.Stop.spec (GF := GF) (hG := hG)) :
    newRaftNode.spec (GF := GF) (hG := hG) := by
  intro E node id nl pre ms γs key wal cv
  wp_start as ⟨#Hzap, #Hsetlg, #Htdok, %Hlg, %Hhb⟩
  iunfold rnLoggerZapOk at Hzap
  iunfold rnSetLoggerOk at Hsetlg
  iunfold rnTimeoutDetectorOk at Htdok
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
  imod mono_list_own_alloc [([] : List EntryModel)] with ⟨%cum, Hcum, #Hlb⟩
  -- (2026-11-03, R2b-3b) the claim on the stop's escrow
  imod token_alloc with ⟨%sc, Hsc⟩
  ihave #Hcum0 := monoListIdxOwn_get (γ := cum) 0 ([] : List EntryModel) (by simp) $$ Hlb
  imod start_bag (V := ReadState) (srvReadStateOk E.γr.raft E.RQ) _ rsc γrs (by simp)
    $$ Hrsc Hrso with #Hrsb
  imod start_bag (V := Loc) (rnSnapMsg ⟨node, id, nl, pre, ms, γs, ⟨γap, cum, cum⟩, cum, γd, key, wal, sc, [], W64 0⟩) _
    msc γms (by simp) $$ Hmsc Hmso with #Hmsb
  imod start_bag (V := Unit) (fun _ => iprop(E.ST ∗ (letI := srvStor (GF := GF) node;
      nodeRunning nl node.cl srvClusterN (1 : Qp).half) ∗
      storage.walOpen (storage.walOf cv.storage') (1 : Qp).half ∗ token wal.app)) _ stc γst (by trivial)
    $$ Hstc Hsto with #Hstb
  imod start_sspsc (V := toApply) apc
    (rnApP E ⟨node, id, nl, pre, ms, γs, ⟨γap, cum, cum⟩, cum, γd, key, wal, sc, [], W64 0⟩)
    (fun _ => iprop(False)) γap $$ Hapc Hapo with ⟨%γsp, #Hspsc, Hprod, Hcons⟩
  -- (2026-11-03, R2b-3b) the claim on the stop's escrow, which `done`'s close announces
  imod alloc_broadcast_chan (E := ⊤)
    (rnDoneEsc ⟨node, id, nl, pre, ms, γs, γsp, cum, γd, key, wal, sc, [], W64 0⟩
      (storage.walOf cv.storage')) γd dnc $$ Hdnc Hdno with Hdc
  icases ownBroadcastChan_open _ _ _ _ $$ Hdc with ⟨%γdi, #Hdint, Hdtok⟩
  ihave #HdcU : ownBroadcastChan (GF := GF) dnc γd
      (rnDoneEsc ⟨node, id, nl, pre, ms, γs, γsp, cum, γd, key, wal, sc, [], W64 0⟩
        (storage.walOf cv.storage')) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdi; iframe #
  ihave Hdc := ownBroadcastChan_close _ _ _ .Pending γdi $$ [$Hdint $Hdtok]
  -- the struct `r`
  (try wp_auto)
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hr0nn⟩
  iStructNamedSuffix «$r0» "R"
  (try wp_auto)
  -- `r.heartbeat != 0`: the ticker
  rw [show (decide (cv.heartbeat' = W64 0) = false) from
    decide_eq_false (fun h0 => by rw [h0] at Hhb; exact absurd Hhb (by decide))]
  (try wp_auto)
  wp_apply (wp_NewTicker cv.heartbeat') as %tk %tch %γt #Htk
  · ipureintro; exact Hhb
  ihave #Htki := isRNTicker_of_time wp_TStop tk tch γt $$ Htk
  (try wp_auto)
  ihave Hsc : rnStopClaim (GF := GF) ⟨node, id, nl, pre, ms, γs, γsp, cum, γd, key, wal, sc, [], W64 0⟩ $$ [Hsc]
  · iunfold rnStopClaim; iexact Hsc
  iapply HΦ
  iexists ⟨node, id, nl, pre, ms, γs, γsp, cum, γd, key, wal, sc, [], W64 0⟩
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
  iframe «$v1» Hprod Hcons Hcum Hcum0 Hdc Hsc
  isplitr
  · ipureintro; simp
  iunfold rnParts
  simp only [named]
  iframe Htki Htdi HdcU
  isplitr
  · ipureintro; exact Hlg
  isplitr
  · iunfold isRNMsgSnapC; iexists γms
    have hsm : rnSnapMsg (GF := GF) ⟨node, id, nl, pre, ms, γs, γsp, cum, γd, key, wal, sc, [], W64 0⟩ =
        rnSnapMsg ⟨node, id, nl, pre, ms, γs, ⟨γap, cum, cum⟩, cum, γd, key, wal, sc, [], W64 0⟩ := by
      unfold rnSnapMsg; rfl
    rw [hsm]; iexact Hmsb
  isplitr
  · iunfold isRNApplyc
    rw [rnApP_cum E ⟨node, id, nl, pre, ms, γs, γsp, cum, γd, key, wal, sc, [], W64 0⟩
      ⟨node, id, nl, pre, ms, γs, ⟨γap, cum, cum⟩, cum, γd, key, wal, sc, [], W64 0⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    iexact Hspsc
  isplitr
  · iunfold isRNReadStateC; iunfold isReadStateC; iexists γrs; iexact Hrsb
  iunfold rnStopBag; iexists γst; iexact Hstb

end proof

end EtcdGrove
end Perennial
