/-
The results of `client/v3/leasing` so far (units 1 and 2: the protocol premise and the lease
cache), restated at top level, with the trust base of each printed in the build log
(`#print axioms`). Every function of `cache.go`, and of `util.go` but `gatherOps` and
`gatherResponseOps` (nested transactions: unit 5), has a `Spec`/`Proof` pair and a linked result
(`Link.lean`, generated).

* **A leased value is stable** (`leasing_leased_value_stable`): under the protocol premise
  (`LeasingProtocol pfx h`, a hypothesis about the deployment: every writer of a data key is a
  leasing client of prefix `pfx`), if the lease key `pfx ++ k` is present at revisions `a ≤ b`
  with one create revision, and its holder committed no transaction in `(a, b]`, then `k` has the
  same record at `a` and `b`.
* **A revoked lease still protects** (`leasing_revoked_protects`): after a lease key's record at
  `a` (e.g. `"REVOKE"`), a transaction of anyone but the holder changes `k` only once that
  incarnation is gone.
* **The lease cache** (`leaseCache_Add`, `leaseCache_Get`, ...): exact transitions of the cache's
  state (`LeaseCacheSt`), with the client's step for each writer and the entries' acquisition
  facts (`entryFacts`); see their specs and `InvLeaseCache.lean`. `EvictRange` evicts `key`, not
  the keys in range, and `evalCmp` is not etcd's comparison: the specs state what the code does
  (findings, `notes/STATUS.md`).

Units 3, 4 and 5 (`txn.go`, `kv.go`): every function has a `Spec`/`Proof` pair and an
unconditional linked result (unit 5 proved the monitors, `NewKV` and `Close`, whose specs the
results of units 3 and 4 had taken as hypotheses).

* **Theorem 1, cached reads** (`leasing_get`, `getCached`; `leasing_cached_get_stable`,
  `leasing_getResult_acq`): a `Get` served from the cache returns the cached answer of an entry
  with its facts (etcd's record of the key at the entry's revision, the lease key with the
  holder's lease); under the protocol premise, while the lease key keeps its incarnation and the
  holder commits nothing, that record is etcd's (if the entry's cached key-value is still its
  acquisition's: this client's own writes change it, theorem 3).
* **Theorem 2, uncached operations** (`leasing_get`'s other cases, `leasing_put`,
  `leasing_delete`, `leasing_Txn_Commit`): what the client's contracts promise, linearizable
  (`lo ≤ r`).
* **Theorem 3, the holder's writes** (`leasing_put`'s `putCommitted`: the cache's step;
  `leasing_update_tracks_put`, `leasing_update_ignoreValue`, `leasing_update_new_key`,
  `leasing_update_out_of_order`): when the cached record tracks etcd's after a put, and the three
  ways it does not (the lease, `WithIgnoreValue`, out-of-order updates).
* **Theorem 4, locally evaluated transactions** (`leasing_Txn_Commit`'s `evalResult`;
  `leasing_evalCmpM_agrees`, `leasing_leaseEvalCmps_agrees`, and the divergences
  `leasing_evalCmpM_absent_lt`, `leasing_evalCmpM_lease`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.Link
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingResults

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **A leased value is stable** (`InvLeasingModel.lean`). -/
theorem leasing_leased_value_stable (pfx k : GoString) (h : LeasingHist) (a b : w64)
    (sa sb : List EtcdKv) (lv lb : EtcdKv) (hk : LeasingDataKey pfx k)
    (hab : sint.Z a ≤ sint.Z b) (hlv : kvOf sa (pfx ++ k) = some lv)
    (hlb : kvOf sb (pfx ++ k) = some lb) (hc : lb.createRev = lv.createRev)
    (hw : ∀ z : Int, sint.Z a < z → z ≤ sint.Z b → h.writer z ≠ lv.lease) :
    LeasingProtocol (GF := GF) pfx h ∗ etcdState a [] sa ∗ etcdState b [] sb ⊢
      ⌜kvOf sb k = kvOf sa k⌝ :=
  leased_value_stable pfx k h a b sa sb lv lb hk hab hlv hlb hc hw

/-- **A revoked lease still protects** (`InvLeasingModel.lean`). -/
theorem leasing_revoked_protects (pfx k : GoString) (h : LeasingHist) (a : w64)
    (sa : List EtcdKv) (lv : EtcdKv) (hk : LeasingDataKey pfx k)
    (hlv : kvOf sa (pfx ++ k) = some lv) (z : Int) (haz : sint.Z a < z) (hz : z < 2 ^ 63)
    (hchg : kvOf (h.st (z - 1)) k ≠ kvOf (h.st z) k) (hw : h.writer z ≠ lv.lease) :
    LeasingProtocol (GF := GF) pfx h ∗ etcdState a [] sa ⊢
      ⌜∀ lz, kvOf (h.st (z - 1)) (pfx ++ k) = some lz → lz.createRev ≠ lv.createRev⌝ :=
  revoked_protects pfx k h a sa lv hk hlv z haz hz hchg hw

/-- `lc.Add(key, resp, op)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Add.lean`). -/
theorem leaseCache_Add : leaseCache.Add.spec (GF := GF) (hG := hG) := leaseCache.wp_Add

/-- `lc.Get(ctx, op)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Get.lean`). -/
theorem leaseCache_Get : leaseCache.Get.spec (GF := GF) (hG := hG) := leaseCache.wp_Get

/-- `lc.Update(key, val, hdr)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Update.lean`). -/
theorem leaseCache_Update : leaseCache.Update.spec (GF := GF) (hG := hG) := leaseCache.wp_Update

/-- `lc.Delete(key, hdr)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Delete.lean`). -/
theorem leaseCache_Delete : leaseCache.Delete.spec (GF := GF) (hG := hG) := leaseCache.wp_Delete

/-- `lc.Evict(key)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Evict.lean`). -/
theorem leaseCache_Evict : leaseCache.Evict.spec (GF := GF) (hG := hG) := leaseCache.wp_Evict

/-- `lc.EvictRange(key, end)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__EvictRange.lean`). -/
theorem leaseCache_EvictRange : leaseCache.EvictRange.spec (GF := GF) (hG := hG) :=
  leaseCache.wp_EvictRange

/-- `lc.Lock(key)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Lock.lean`). -/
theorem leaseCache_Lock : leaseCache.Lock.spec (GF := GF) (hG := hG) := leaseCache.wp_Lock

/-- `lc.LockWriteOps(ops)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__LockWriteOps.lean`). -/
theorem leaseCache_LockWriteOps : leaseCache.LockWriteOps.spec (GF := GF) (hG := hG) :=
  leaseCache.wp_LockWriteOps

/-- `lc.Rev(key)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Rev.lean`). -/
theorem leaseCache_Rev : leaseCache.Rev.spec (GF := GF) (hG := hG) := leaseCache.wp_Rev

/-- `lc.clearOldRevokes(ctx)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__clearOldRevokes.lean`). -/
theorem leaseCache_clearOldRevokes : leaseCache.clearOldRevokes.spec (GF := GF) (hG := hG) :=
  leaseCache.wp_clearOldRevokes

/-! ## Units 3 and 4: the leasing KV -/

/-- **Theorems 1 and 2 for reads**: `lkv.Get(ctx, key, opts...)` returns `getOutcome`: the
client's answer (linearizable unless serializable), the cache's (`getCached`: an entry with its
facts), an acquisition's (`getAcquired`: etcd's record at a revision `≥ lo`), or a failed
acquisition's (`getNotAcquired`: etcd's answer to `OpGet(key)`, the options ignored, a finding). -/
theorem leasing_get : leasingKV.Get.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_Get

/-- **Theorem 2 and 3 for puts**: `lkv.Put(ctx, key, val, opts...)` returns an error or the put
committed at a revision `r ≥ lo` on etcd's state at `r - 1` (`putCommitted`), with the cache's
step (`LeaseEntry.update` of the key's entry). -/
theorem leasing_put : leasingKV.Put.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_Put

/-- **Theorem 2 for deletes**: `lkv.Delete(ctx, key, opts...)` returns an error or the delete of
the range committed at a revision `r ≥ lo` (`deleteCommitted`). -/
theorem leasing_delete : leasingKV.Delete.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_Delete

/-- **Theorems 2 and 4 for transactions**: `txn.Commit()` returns the cache's evaluation
(`evalResult`: `leaseEvalCmps` of the cached entries, the cached gets' answers, at the cache's
header) or the client's answer for the user's transaction (`txnCommitResult`). -/
theorem leasing_Txn_Commit : txnLeasing.Commit.spec (GF := GF) (hG := hG) :=
  txnLeasing.wp_Commit

/-- `lkv.Do(ctx, op)`, by the operation's kind. -/
theorem leasing_Do : leasingKV.Do.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_Do

/-- **Unit 5, the leasing KV's constructor**: `NewKV(cl, pfx, opts...)` returns the `KV` interface
value of a leasing KV (`isLeasingKV`) with every reader slot of its cache, the whole "open"
token, the close function's spec (`leasingCloseFn`) and `waitSession`'s error (`newKVResult`);
the session monitor and `clearOldRevokes` running. -/
theorem leasing_NewKV : NewKV.spec (GF := GF) (hG := hG) := wp_NewKV

/-- `lkv.Close()` (`Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Close.lean`). -/
theorem leasing_Close : leasingKV.Close.spec (GF := GF) (hG := hG) := leasingKV.wp_Close

/-- **`waitRescind`'s outcomes** (a finding): `nil` after a delete of the lease key above `rev`, or
`nil` with no promise (the watch closed without a delete event). -/
theorem leasing_waitRescind : leasingKV.waitRescind.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_waitRescind

/-- The lease monitor (`get`'s goroutine) and the session monitor (`NewKV`'s) return. -/
theorem leasing_monitorLease : leasingKV.monitorLease.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_monitorLease

theorem leasing_monitorSession : leasingKV.monitorSession.spec (GF := GF) (hG := hG) :=
  leasingKV.wp_monitorSession

/-- `lkv.Txn(ctx)` (`Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Txn.lean`). -/
theorem leasing_Txn : leasingKV.Txn.spec (GF := GF) (hG := hG) := leasingKV.wp_Txn

/-- **Theorem 1's corollary** (`InvLeasingResults.lean`). -/
theorem leasing_cached_get_stable (pfx key : GoString) (h : LeasingHist) (e : LeaseEntry) (b : w64)
    (sb : List EtcdKv) (hk : LeasingDataKey pfx key) (hrev : sint.Z e.rev ≤ sint.Z b)
    (hw : ∀ z : Int, sint.Z e.rev < z → z ≤ sint.Z b → h.writer z ≠ e.lease) :
    LeasingProtocol (GF := GF) pfx h ∗ entryFacts pfx key e ∗ etcdState b [] sb ⊢
      ∃ (s : List EtcdKv) (lv : EtcdKv), □ etcdState e.rev [] s ∗
        ⌜kvOf s (pfx ++ key) = some lv ∧ lv.lease = e.lease ∧
          ∀ lb, kvOf sb (pfx ++ key) = some lb → lb.createRev = lv.createRev → kvOf sb key = e.acq⌝ :=
  cached_get_stable pfx key h e b sb hk hrev hw

/-- The cached get's answer of an entry whose cached key-value is its acquisition's. -/
theorem leasing_getResult_acq (o : OpFull) (e : LeaseEntry) (h : e.kv = e.acq) :
    getResult o e = if getEmpty o.base e.kvs then none
      else e.acq.map (fun v => if o.keysOnly then { v with value := [] } else v) :=
  getResult_acq o e h

/-- **Theorem 3**: `Update` tracks the holder's put iff the put keeps the cached lease. -/
theorem leasing_update_tracks_put (c : CachedKv) (r : w64) (valSl : GoSlice) (key val : GoString)
    (l : w64) (s : List EtcdKv) (hwf : EtcdStateWf [] s) (hrec : kvOf s key = some c.kv)
    (hmod : sint.Z c.kv.modRev < sint.Z r) :
    kvOf (applyTxnOp r s (.put key val l)).1 key = some (c.bump r valSl val).kv ↔
      l = c.kv.lease :=
  update_tracks_put c r valSl key val l s hwf hrec hmod

/-- **Theorem 3, `WithIgnoreValue`** (a finding): the cache serves the empty value. -/
theorem leasing_update_ignoreValue (c : CachedKv) (r : w64) (valSl : GoSlice) (key : GoString)
    (l : Option w64) (s : List EtcdKv) (hwf : EtcdStateWf [] s) (hrec : kvOf s key = some c.kv)
    (hmod : sint.Z c.kv.modRev < sint.Z r) :
    kvOf (applyTxnOp r s (.putIgnVal key l)).1 key = some (c.bump r valSl []).kv ↔
      c.kv.value = [] ∧ l.getD c.kv.lease = c.kv.lease :=
  update_ignoreValue c r valSl key l s hwf hrec hmod

/-- **Theorem 3, a key cached as absent**. -/
theorem leasing_update_new_key (p : Loc) (keySl valSl : GoSlice) (r : w64) (key val : GoString)
    (l : w64) (s : List EtcdKv) (hwf : EtcdStateWf [] s) (habs : kvOf s key = none)
    (hr : 0 < sint.Z r) :
    kvOf (applyTxnOp r s (.put key val l)).1 key =
        some ((freshKv p keySl key r).bump r valSl val).kv ↔ l = W64 0 :=
  update_new_key p keySl valSl r key val l s hwf habs hr

/-- **Theorem 3, out-of-order updates** (a finding). -/
theorem leasing_update_out_of_order (c : CachedKv) (r1 r2 : w64) (sl1 sl2 : GoSlice)
    (v1 v2 : GoString) (h1 : sint.Z c.kv.modRev < sint.Z r1) (h12 : sint.Z r1 < sint.Z r2) :
    (c.bump r2 sl2 v2).kv = { c.kv with version := c.kv.version + W64 1, modRev := r2, value := v2 } ∧
    ((c.bump r2 sl2 v2).bump r1 sl1 v1).kv =
      { c.kv with version := c.kv.version + W64 1 + W64 1, modRev := r2, value := v2 } :=
  update_out_of_order c r1 r2 sl1 sl2 v1 v2 h1 h12

/-- **Theorem 4: when the cache's comparison is etcd's**. -/
theorem leasing_evalCmpM_agrees (s : List EtcdKv) (m : CmpModel) (hwf : EtcdStateWf [] s)
    (hr : m.rangeEnd = []) (hl : m.target ≠ .lease)
    (habs : kvOf s m.key = none → m.target ≠ .value ∧ m.num = W64 0) :
    leaseCmpHolds m (kvOf s m.key) = cmpHolds s m :=
  evalCmpM_agrees s m hwf hr hl habs

/-- **Theorem 4: a transaction's comparisons**. -/
theorem leasing_leaseEvalCmps_agrees (st : LeaseCacheSt) (s : List EtcdKv) (hwf : EtcdStateWf [] s)
    (ms : List CmpModel)
    (hc : ∀ m ∈ ms, m.rangeEnd = [] ∧ m.target ≠ .lease ∧
      (∃ e, st.entries !! m.key = some e ∧ e.kv = kvOf s m.key) ∧
      (kvOf s m.key = none → m.target ≠ .value ∧ m.num = W64 0)) :
    leaseEvalCmps st ms = (ms.all (cmpHolds s), true) :=
  leaseEvalCmps_agrees st s hwf ms hc

/-- **Theorem 4, the divergences** (findings): an absent key, a lease comparison. -/
theorem leasing_evalCmpM_absent_lt (k : GoString) :
    leaseCmpHolds (compareM (cmpKeyM .create k) .lt (.num (W64 5))) none = false ∧
      cmpHolds [] (compareM (cmpKeyM .create k) .lt (.num (W64 5))) = true :=
  evalCmpM_absent_lt k

theorem leasing_evalCmpM_lease (v : EtcdKv) (hv : v.lease = W64 7) :
    leaseCmpHolds (compareM (cmpKeyM .lease v.key) .eq (.num (W64 8))) (some v) = true ∧
      cmpKv (compareM (cmpKeyM .lease v.key) .eq (.num (W64 8))) v = false :=
  evalCmpM_lease v hv

end results

end leasing
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.leasing.leasing_leased_value_stable
#print axioms Perennial.EtcdGrove.leasing.leasing_revoked_protects
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Add
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Get
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Update
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Delete
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Evict
#print axioms Perennial.EtcdGrove.leasing.leaseCache_EvictRange
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Lock
#print axioms Perennial.EtcdGrove.leasing.leaseCache_LockWriteOps
#print axioms Perennial.EtcdGrove.leasing.leaseCache_Rev
#print axioms Perennial.EtcdGrove.leasing.leaseCache_clearOldRevokes
#print axioms Perennial.EtcdGrove.leasing.leasing_get
#print axioms Perennial.EtcdGrove.leasing.leasing_put
#print axioms Perennial.EtcdGrove.leasing.leasing_delete
#print axioms Perennial.EtcdGrove.leasing.leasing_Txn_Commit
#print axioms Perennial.EtcdGrove.leasing.leasing_Do
#print axioms Perennial.EtcdGrove.leasing.leasing_Txn
#print axioms Perennial.EtcdGrove.leasing.leasing_NewKV
#print axioms Perennial.EtcdGrove.leasing.leasing_Close
#print axioms Perennial.EtcdGrove.leasing.leasing_waitRescind
#print axioms Perennial.EtcdGrove.leasing.leasing_monitorLease
#print axioms Perennial.EtcdGrove.leasing.leasing_monitorSession
#print axioms Perennial.EtcdGrove.leasing.leasing_cached_get_stable
#print axioms Perennial.EtcdGrove.leasing.leasing_getResult_acq
#print axioms Perennial.EtcdGrove.leasing.leasing_update_tracks_put
#print axioms Perennial.EtcdGrove.leasing.leasing_update_ignoreValue
#print axioms Perennial.EtcdGrove.leasing.leasing_update_new_key
#print axioms Perennial.EtcdGrove.leasing.leasing_update_out_of_order
#print axioms Perennial.EtcdGrove.leasing.leasing_evalCmpM_agrees
#print axioms Perennial.EtcdGrove.leasing.leasing_leaseEvalCmps_agrees
#print axioms Perennial.EtcdGrove.leasing.leasing_evalCmpM_absent_lt
#print axioms Perennial.EtcdGrove.leasing.leasing_evalCmpM_lease
