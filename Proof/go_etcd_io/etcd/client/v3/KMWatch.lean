/-
**A client watcher of etcd's KV meets the cache's watcher contracts** (D48, 2026-10-26).
Lean-first, no Rocq counterpart.

`isEtcdWatcher_of_km`: a `*watcher` of etcd's KV `γ.kv` (`isKvWatcher`), with the adapter's
invariant (`kmInv γ`, `EtcdModelKV.lean`), meets the cache's watch contract (`isEtcdWatcher`,
`cache/v3/InvEtcd.lean`) at the adapter's model (`etcdModelOfKV γ`), for a non-empty prefix:
the call is `watcher.Watch.spec`'s, with the adapter's read update after the floor
the caller knows (`km_read_au` at `km_reached_lb`'s changes of `etcdRead (rev - 1)`), and each
response, a read of a state the client saw (`watchStateRespOk`), is etcd's response of the
cache's contract (`watchRespOk_of_km`):
* a progress notification past the cursor is a step without events (`kmStep`) of the log of the
  state it read, through its revision (`kvLogOkTo`); at the watch's start, the caller's floor;
* events are the range's events of that log (`rangeEvents_take`: mvcc's watch events of the
  prefix's range `pfxRange`), so a chain of steps (`km_chain`), one per revision.
`isEtcdProgressNotifier_of_km`: `RequestProgress` from `isKvWatcher` (`ServerWatcher.lean`'s).
The lemmas that rest on no linked result (`etcdWatchElem_of_km` and what it needs) are in
`KMWatchDefs.lean` (2026-11-26), so that defs modules can use them.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KMWatchDefs
public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver mvcc txn

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A client watcher of etcd's KV meets the cache's watcher contract** at the adapter's model
(see the file header), for a non-empty prefix (`watcher.Watch.spec`'s
prefix-watch condition): the channel `Watch` returns, its elements etcd's
(`etcdWatchElem_of_km`). -/
theorem isEtcdWatcher_of_km (w : Loc) (γ : KMNames) (pfx : GoString) (hp : pfx ≠ []) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isKvWatcher w γ.kv ∗ kmInv γ ⊢
    isEtcdWatcher (EM := etcdModelOfKV γ) (watcherIfaceOf w) pfx := by
  iintro ⟨#P1, #P2, #P3, #Hw, #Hinv⟩
  unfold isEtcdWatcher
  iintro !> %ctx %cs %key %sl %gs %rev %Φ !> ⟨#Hctx, #HctxO, #Hopts, %Hpre, #Hrd⟩ HΦ
  obtain ⟨hpw, hnp, hrev, hsz⟩ := Hpre
  unfold OpFull.isPrefixWatch at hpw
  simp only [decide_eq_true_eq, hp, if_false] at hpw
  obtain ⟨ht, hr, -, -, hpk, hfr, hfp, hfd, hkey, hend⟩ := hpw
  ihave #Hreach := etcdRead_reached (EM := etcdModelOfKV γ) (rev - W64 1) $$ Hrd
  imod km_reached_lb γ (rev - W64 1) $$ Hreach with ⟨%l0, #Hl0, -⟩
  ihave #Hau := km_read_au γ l0 $$ [$Hinv $Hl0]
  -- (G2) the watcher's environment explicit, no auth bound (`n = 0`)
  ihave #Hw' := Hw
  iunfold isKvWatcher at Hw'
  icases Hw' with ⟨%V, #Hcw, %Hkst⟩
  ihave #HctxO' := HctxO
  iunfold metadata.outgoingCtxOkC at HctxO'
  icases HctxO' with ⟨%om, #Hom⟩
  iapply (v3.watcher.wp_Watch w V γ.kv ctx cs om key sl gs rev (kmSeenQ γ l0) 0) $$ [] [HΦ]
  · iframe #
    isplitr
    · ipureintro; exact Hkst
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    isplitr
    · ipureintro
      refine ⟨?_, hnp, by omega, ?_⟩
      · refine OpFull.isRangeWatchP_of ?_
        unfold OpFull.isRangeWatch; simp only [decide_eq_true_eq]
        exact ⟨ht, hr, hpk, hfr, hfp, hfd⟩
      · exact hsz
    isplitr
    · iintro !> %h
      exact absurd h.2 (Nat.lt_irrefl 0)
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    iexact Hau
  inext
  -- (G2) a non-empty key's range is its own (`watchNorm_of_ne`)
  rw [OpFull.watchNorm_of_ne _ (by rw [hkey]; exact hp)]
  iintro %ch %γw ⟨#Hs, Hc, Hi⟩
  iapply HΦ
  isplitr
  · unfold isEtcdWatchChan
    iexists watchStateElemP _ γw (opWatchModel key gs) (kmSeenQ γ l0) _
    iframe Hs
    iintro !> %i %v H
    ihave H := watchStateElemP_elem _ γw (opWatchModel key gs) (kmSeenQ γ l0) _ i v $$ H
    imodintro
    iapply etcdWatchElem_of_km γ l0 pfx hp (opWatchModel key gs) rev hkey hend hr _ γw _ i v
      $$ [Hreach H]
    iframe Hreach H
  unfold etcdWatchConsumer
  iexists []
  iframe Hc Hi
  ipureintro; rfl

/-- **A client watcher of etcd's KV is the cache's progress notifier** (`isKvWatcher`'s client
watcher, `isEtcdProgressNotifier_of_watcher`). -/
theorem isEtcdProgressNotifier_of_km (w : Loc) (γk : KVNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isKvWatcher w γk ⊢
    isEtcdProgressNotifier (watcherIfaceOf w) := by
  iintro ⟨#P1, #P2, #P3, #Hw⟩
  iunfold isKvWatcher at Hw
  icases Hw with ⟨%V, #Hcw, -⟩
  iapply isEtcdProgressNotifier_of_watcher v3.watcher.wp_RequestProgress V w $$ [P1 P2 P3 Hcw]
  iframe #

end bridge

end client
end EtcdGrove
end Perennial
