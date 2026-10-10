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
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
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
