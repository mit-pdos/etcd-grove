/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean` (backend-snapshot B4,
2026-11-21; until then a trust-boundary axiom, D22 S-f; `notes/backend-snapshot-plan.md`). `b.Snapshot()`
registers the caller's `R` and observation in the commit invariant (`RegSnap.lean`'s `reg_register`)
before its own `Commit()`, whose commit point (or no-op) arms it (`Commit.specCnt`'s counter); then,
read-locking `b.mu` with the slot the caller's `rdTok` lends (`bmSlot`), it begins bbolt's read
transaction, whose update is fired from the commit invariant's half of the committed data `D`, where
the armed registration is taken out (`reg_take`: `R` back, `Q` of `D`) and the invariant's reader lower
bound of the compaction keys' flag read (`fkRd`). The snapshot's two channels are broadcast channels,
`stopc`'s close right in the invariant `snapN` (`InvSnapshot.lean`'s `snapAt`); the warning goroutine
(its own fork's fuel) ticks at an interval at least `minSnapshotWarningTimeout` (positive: the backend's
package fact holds its value) until `stopc` closes, then observes `snapshotTransferSec` and closes
`donec`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Commit
public import Spec.go_etcd_io.bbolt.DB__Begin
public import Spec.go_etcd_io.bbolt.Tx__Size
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.String
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RegSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

set_option linter.iris.dupNamespace false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]
variable [github_com.dustin.go_humanize.Assumptions]

private instance fkRd_timeless (γ : BNames) (P : BParams) (rv : RView) :
    Timeless (fkRd (GF := GF) γ P rv) := by
  unfold fkRd fkVR; infer_instance

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- bbolt's `DB.Begin(false)` outside the batch lock, in the backend's vocabulary, at `theFs`: the
read update is fired from the commit invariant's half of the committed data `D` (the backend open, so
not stopped), where the caller's armed registration is taken out (`reg_take`: `R` back, `Q` of `D`)
and the invariant's reader lower bound of the compaction keys' flag at `D` read. -/
private theorem bbolt.snapGlue_DBBegin (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
      [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions], bbolt.DB.Begin.spec (GF := GF) (hG := hG)) :
  ∀ (db : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (path : GoString) (qo : Qp) (i n : Nat)
    (R : IProp GF) (Q : ObsQ),
  γ.db.ns = dbNs path →
  {{ isDB db γ.db ∗ threadTok ∗ cmtInv γ P W Pk ∗ bOpen γ qo ∗ regTok γ P i n R Q ∗
      cntLb γ (n + 1) ∗ £ 1 ∗ £ 1 }}
    (App (Val (db @!! go.GoType.PointerType go_etcd_io.bbolt.DB.ty @!! go!"Begin")) (Val #false))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ D : backend.Data, txLive tx γ.db 1 (bbolt.TxView.ro D) ∗
        bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, W64 0⟩) ∗ ⌜obsAt P Q D⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }} := by
  intro db γ P W Pk path qo i n R Q hns
  have hE : (↑cmtN : CoPset) ⊆ ⊤ \ ↑γ.db.ns := by rw [hns]; exact cmtN_dbNs path
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.isDB, onFs_none hfs]
    iintro %Φ ⟨H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.isDB, backend.txLive, onFs_some hfs]
    iintro %Φ ⟨#Hdb, Htok, #Hinv, Hopen, Hrg, #Hlb, Hlc1, Hlc2⟩ HΦ
    ihave Hau : AU <{ ∃∃ (q : Qp) (D : backend.Data), bbolt.boltState γ.db q D }> @ ⊤ \ ↑γ.db.ns, ∅
        <{ bbolt.boltState γ.db q D,
           COMM bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, W64 0⟩) ∗ ⌜obsAt P Q D⌝ }> $$
        [Hopen Hrg Hlc1 Hlc2]
    · iauintro
      unfold atomic_acc
      iunfold cmtInv at Hinv
      iinv Hinv with Hb Hclose
      try exact hE
      iunfold cmtBody at Hb
      icases Hb with (⟨%Dc, >Hh, >#Hfk, Hregs⟩ | >#Hst)
      rotate_left
      · iexfalso
        iapply bOpen_stopped γ qo $$ [$Hopen $Hst]
      isimp only [backend.dbHalf, onFs_some hfs] at Hh
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hcl
      isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
      iexists (1 : Qp).half, Dc
      iframe Hh
      isplit
      · iintro Hh
        imod Hcl with -
        imod Hclose $$ [Hh Hregs] with -
        · inext
          iunfold cmtBody
          ileft
          iexists Dc
          isimp only [backend.dbHalf, onFs_some hfs]
          iframe Hh Hregs Hfk
        imodintro
        iframe Hopen Hrg Hlc1 Hlc2
      · iintro Hh
        imod Hcl with -
        imod (reg_take γ P W Pk i n R Q Dc _) $$ [$Hrg $Hlb $Hlc1 $Hlc2 $Hregs] with ⟨Hregs, HR, %HQ⟩
        imod Hclose $$ [Hh Hregs] with -
        · inext
          iunfold cmtBody
          ileft
          iexists Dc
          isimp only [backend.dbHalf, onFs_some hfs]
          iframe Hh Hregs Hfk
        imodintro
        iframe Hopen HR Hfk
        ipureintro; exact HQ
    have h' := h db γ.db false (fun D => iprop(bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, W64 0⟩) ∗
      ⌜obsAt P Q D⌝))
    simp only [Bool.false_eq_true, ↓reduceIte] at h'
    wp_apply h' $$ [$Hdb $Htok $Hau] as %tx %err Hr
    icases Hr with (⟨%He, -, %D, Htx, Hq⟩ | ⟨%He, -, -⟩)
    · iapply HΦ
      ileft
      isplitr; · ipureintro; exact He
      iexists D
      iframe Htx Hq
    · iapply HΦ
      iright; ipureintro; exact He.1

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- bbolt's `Tx.Size` of a read transaction in the backend's vocabulary, at `theFs`
(`snapshot__Size.lean`'s glue). -/
private theorem bbolt.snapGlue_TxSizeRo (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
      [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions], bbolt.Tx.Size.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data),
  {{ txLive (GF := GF) tx γ q (bbolt.TxView.ro D) }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; txLive tx γ q (bbolt.TxView.ro D) }} := by
  intro tx γ q D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.txLive, onFs_none hfs]
    iintro %Φ H HΦ
    iexfalso; iexact H
  · simp only [backend.txLive, onFs_some hfs]
    iintro %Φ Hl HΦ
    wp_apply (h tx γ q (TxView.ro D)) $$ [$Hl] as %n ⟨Hl, -⟩
    iapply HΦ; iexact Hl

/-- `b.Snapshot()`: see the file header. -/
theorem backend.backend.Snapshot.wp_proof
    (hCommit : backend.batchTxBuffered.Commit.specCnt (GF := GF) (hG := hG))
    (hBegin : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.DB.Begin.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hSize : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Size.spec (GF := GF) (hG := hG))
    (hNow : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (hNewTicker : _root_.Perennial.time.NewTicker.spec (GF := GF) (hG := hG))
    (hStop : _root_.Perennial.time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (hSince : _root_.Perennial.time.Since.spec (GF := GF) (hG := hG))
    (hDuration : zap.Duration.spec (GF := GF) (hG := hG))
    (hInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hBytes : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hString : zap.String.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hSeconds : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    backend.backend.Snapshot.spec (GF := GF) (hG := hG) := by
  replace hBegin := bbolt.snapGlue_DBBegin hBegin
  replace hSize := bbolt.snapGlue_TxSizeRo hSize
  intro hTB γ P W Pk b qo R Q
  wp_start as ⟨#Hb, Hopen, Hwb, Htok, Hrd, HR, #Hwand⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hw : obsWand γ P W Pk R Q $$ []
  · unfold obsWand; iexact Hwand
  iclear Hwand
  icases isBackend_cmtInv γ P W Pk b $$ Hb with ⟨#Hcmt, %path, %hns⟩
  ihave #Hb' := Hb
  iunfold isBackend at Hb'
  icases Hb' with ⟨%t, %rt, %tm, %db, %lg, %h, #Ht, -, -, #Hlg, #Hlgn, -, -, -, -, -, -, -, -, -,
    -, #Hmug, #Hisdb, -, ⟨%path', #HdbAt, -⟩, -, -⟩
  -- the package's facts the goroutine reads
  ihave Hi : (backendInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, -, -, -, ⟨%hst, #Hgst, #Hsst⟩, #Hmin⟩
  unfold histSpec
  -- (1) the registration
  imod (reg_register γ P W Pk qo R Q) $$ [$Hcmt $Hopen $HR $Hw] with ⟨Hopen, %i, %n, Hrg, #Hlb⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  -- (2) `b.batchTx.Commit()`, which arms it
  wp_apply (hCommit γ P W Pk b t qo iprop(True) iprop(True) n) $$ [$Hb $Ht $Hopen $Hwb $Hlb]
    as ⟨Hopen, -, #Hlb'⟩
  · iapply commitReq_true
  -- (3) `b.mu.RLock()`, with the slot the caller's reader token lends
  unfold rdTok
  icases Hrd with ⟨%rt2, #Hrt2, Hrmu, Hcr, Hbm⟩
  unfold bmSlot
  icases Hbm with ⟨%db2, #HdbAt2, Hbmu⟩
  iunfold bDB at HdbAt2
  icases HdbAt2 with ⟨%p2, #HdbAt2⟩
  iunfold bDBAt at HdbAt HdbAt2
  ihave %Hg := dghostVar_agree γ.dbf ((db, path') : Loc × GoString) _ ((db2, p2) : Loc × GoString) _
    $$ HdbAt HdbAt2
  simp only [Prod.mk.injEq] at Hg
  obtain ⟨hdb, -⟩ := Hg
  subst hdb
  wp_apply (lc := 2) sync.RWMutex.wp_RLock $$ [$Hbmu] as ⟨Hrl, Hdbf⟩
  -- (4) `b.db.Begin(false)`, its update fired from the commit invariant
  wp_apply (hBegin db γ P W Pk path qo i n R Q hns) $$
    [$Hisdb $Htok $Hcmt $Hopen $Hrg $Hlb' $Hlc1 $Hlc2] as %tx %err Hr
  icases Hr with (⟨%Herr, %D, Htx, Hopen, HR, #Hfk, %HQ⟩ | %Herr)
  rotate_left
  · -- an error: `lg.Fatal`
    rcases err with ei | _
    · wp_auto
      wp_apply hError as %f -
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      wp_apply hFatal lg $$ [] as %v Hf
      · iexact Hlgn
      iexfalso
      iexact Hf
    · exact absurd rfl Herr
  subst Herr
  wp_auto
  -- (5) the channels, as broadcast channels
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsc Hsoc with Hspend
  icases ownBroadcastChan_open _ _ _ _ $$ Hspend with ⟨%γsb, #Hsbi, Hspend⟩
  ihave #HscU := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γsb $$ [$Hsbi]
  ihave Hspend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γsb $$ [$Hsbi $Hspend]
  wp_apply chan.wp_make1 (V := Unit) as %dc %γdc ⟨#Hdc, %_, Hdoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γdc dc $$ Hdc Hdoc with Hdpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hdpend with ⟨%γdb, #Hdbi, Hdpend⟩
  ihave #HdcU := ownBroadcastChan_close dc γdc iprop(True) Broadcast.Unknown γdb $$ [$Hdbi]
  ihave Hdpend := ownBroadcastChan_close dc γdc iprop(True) Broadcast.Pending γdb $$ [$Hdbi $Hdpend]
  try wp_auto
  -- (6) `tx.Size()`
  wp_apply (hSize tx γ.db 1 D) $$ [$Htx] as %nb Htx
  try wp_auto
  -- (7) the warning goroutine, its own fork's fuel
  ipersist b
  ipersist stopc
  ipersist donec
  ipersist dbBytes
  wp_apply wp_fork $$ [Hdpend]
  · wp_auto
    wp_apply wp_with_defer as %defer2 defer2
    (try wp_auto)
    wp_apply wp_float64_div as %_ -
    (try wp_auto)
    wp_apply wp_float64_mul as %_ -
    (try wp_auto)
    wp_apply wp_ArbitraryInt as %x -
    have h30 : sint.Z (W64 30000000000) = 30000000000 := by decide
    -- the ticker's interval: at least `minSnapshotWarningTimeout`, positive
    wp_join iprop(∃ d : w64, warningTimeout_ptr ↦ d ∗ ⌜0 < sint.Z d⌝) with [warningTimeout]
      as ⟨%d, warningTimeout, %Hd⟩
    · iexists _; iframe warningTimeout; ipureintro; omega
    · iexists _; iframe warningTimeout; ipureintro; omega
    wp_apply hNow as %st -
    wp_apply (lc := 2) hNewTicker d as %tk %tch %γt #Htk
    · ipureintro; exact Hd
    ihave #Htk' := Htk
    iunfold _root_.Perennial.time.isTicker at Htk'
    icases Htk' with ⟨#HtC, #HtI, #HtR, #Htbag⟩
    try wp_auto
    wp_for
    try wp_auto
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a tick: a warning
      simp only [chan.blockingClausePre]
      iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
      inext
      iintro %tm0 -
      wp_auto_lc 2
      wp_apply hSince as %dur -
      wp_apply hDuration as %f1 -
      wp_apply hInt64 as %f2 -
      wp_apply hBytes as %str -
      wp_apply hString as %f3 -
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      wp_apply hWarn lg $$ []
      · iexact Hlgn
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `stopc` closed: observe and return
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γsc
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hsc
      iapply broadcast_chan_receive _ _ _ _ _ $$ HscU
      iintro ⟨-, -⟩
      try wp_auto
      wp_apply hSince as %dur -
      wp_apply hSeconds as %secs -
      try wp_auto
      wp_apply Hsst
      wp_for_post
      try wp_auto
      wp_apply hStop tk $$ []
      · iexists tch, γt; iexact Htk
      try wp_auto
      wp_apply (wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv
        (go.GoType.StructType [])) dc γdc iprop(True)) $$ [$Hdpend] as -
      · imodintro; itrivial
      try wp_auto
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  try wp_auto
  -- the snapshot's ghost variable, whole, and its invariant with `stopc`'s close right
  imod (ghostVar_alloc (GF := GF) ((tx, γ.db) : Loc × DBNames)) with ⟨%γs, Hg⟩
  imod inv_alloc snapN ⊤ iprop(ownBroadcastChan (GF := GF) sc γsc iprop(True) .Pending ∨
      ghostVar γs 1 (tx, γ.db)) $$ [Hspend] with #Hinv
  · inext; ileft; iexact Hspend
  -- (8) the `*snapshot`, its fields read-only for good
  wp_alloc sp as Hsp
  iStructNamed Hsp
  ipersist Tx
  ipersist stopc
  ipersist donec
  try wp_auto
  -- the deferred `b.mu.RUnlock()`
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl $Hdbf] as Hbmu
  try wp_auto
  iapply HΦ
  iframe Hopen HR Hfk
  isplitl [Hg Htx]
  · unfold snapOpen snapOpenQ
    iexists γs, tx, γ.db
    iframe Hg Htx
    unfold snapAt
    iexists sc, dc, γsc, γdc
    iframe Tx stopc donec HscU HdcU Hinv
  isplitl [Hrmu Hcr Hbmu]
  · iexists rt2
    iframe Hrt2 Hrmu Hcr
    iexists db
    iframe Hbmu
    unfold bDB bDBAt
    iexists path'
    iexact HdbAt
  ipureintro; exact HQ

end proof

end EtcdGrove
end Perennial
