/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchersLoop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchers
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__size
public import Spec.time.NewTicker
public import Spec.time.Ticker__Stop
public import Spec.time.Ticker__Reset
public import Spec.time.Since

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.syncWatchersLoop.wp_proof
    (hNew : time.NewTicker.spec (GF := GF) (hG := hG))
    (hStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (hSize : mvcc.watcherGroup.size.spec (GF := GF) (hG := hG))
    (hSync : mvcc.watchableStore.syncWatchers.spec (GF := GF) (hG := hG))
    (hSince : time.Since.spec (GF := GF) (hG := hG))
    (hReset : time.Ticker.Reset.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.syncWatchersLoop.spec (GF := GF) (hG := hG) := by
  intro s st γ
  wp_start as ⟨#Hws, HR, Hdone⟩
  ihave #Hws0 := Hws
  iunfold mvcc.isWatchableStore at Hws0
  iNamedSuffix Hws0 "W"
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hper, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hNew as %t #Ht
  · ipureintro; decide
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨-, %tch, %γt, #HC, #Hbag⟩
  ihave #Hstop := HstopW
  iunfold mvcc.isStopChan at Hstop
  icases Hstop with ⟨%γs, #Hstop⟩
  (try wp_auto)
  wp_for
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hsr0, Hmur⟩
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hmur] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP, %Hset⟩
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  wp_apply time.wp_Now as %tm -
  (try wp_auto)
  wp_apply hSize $$ [$Hunsynced] as ⟨Hunsynced, %Hsz⟩
  (try wp_auto)
  ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
      [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hmur
  · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iframe HP; ipureintro; exact Hset
  (try wp_auto)
  ihave HR : mvcc.watchReader s st γ $$ [Hsr0 Hmur]
  · iunfold mvcc.watchReader; iframe
  wp_join iprop(∃ n : w64, unsyncedWatchers_ptr ↦ n ∗ mvcc.watchReader s st γ ∗ s_ptr ↦ s)
    with [unsyncedWatchers HR s] as ⟨%n, unsyncedWatchers, HR, s⟩
  · (try wp_auto)
    wp_apply hSync $$ [$Hws $HR] as %n HR
    (try wp_auto)
    wp_join_done
  wp_apply +noauto hSince as %d %Hd
  wp_auto_lc 2
  wp_apply hReset $$ [$Ht]
  · ipureintro; decide
  wp_join with [delayTicker lastUnsyncedWatchers unsyncedWatchers syncDuration]
  · wp_if_destruct
    · wp_apply hReset $$ [$Ht]
      · ipureintro; exact Hd
      wp_join_done
    · wp_join_done
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tm' -
    wp_auto
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstop
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstop
    iintro -
    wp_auto
    wp_for_post
    wp_apply hStop $$ [$Ht]
    wp_apply mvcc.wp_wsDone s $$ [$Hsync $Hdone]
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
