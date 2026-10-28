/-
**The cache's client, from the client's specs** (D48, 2026-10-26). Lean-first, no Rocq
counterpart.

`isEtcdClient_of_km`: a `*clientv3.Client` whose `KV` field is a `*kv` of etcd's KV `γ.kv`
(`isKv`, any `dup`: the cache only reads) and whose `Watcher` field a client watcher of it
(`isKvWatcher`) meets the cache's client contract (`isEtcdClient`, `cache/v3/InvNew.lean`) at the
adapter's model (`etcdModelOfKV γ`, with its invariant `kmInv γ`), for a non-empty prefix not all
`0xff`: its gets (`isEtcdKVE_of_km`, any context: the watcher's `ctxErrClientAllW`), its watches
(`isEtcdWatcher_of_km`) and its progress requests (`isEtcdProgressNotifier_of_km`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KMGet
public import Proof.go_etcd_io.etcd.client.v3.KMWatch
public import Proof.go_etcd_io.etcd.cache.v3.InvNew

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- A client watcher's contexts' errors are client errors (`watchConnFacts`' `ctxErrClientAllW`). -/
theorem ctxErrClientAll_of_kvWatcher (w : Loc) (γk : KVNames) :
    isKvWatcher (GF := GF) w γk ⊢ ctxErrClientAll := by
  iintro #Hkw
  iunfold isKvWatcher at Hkw
  icases Hkw with ⟨%V, #Hw, -⟩
  iunfold isClientWatcher at Hw
  icases Hw with ⟨%cs, %vs, -, -, -, -, -, -, -, Hsf, -⟩
  iunfold watchSrvFacts at Hsf
  icases Hsf with ⟨-, Hcf⟩
  iunfold watchConnFacts at Hcf
  icases Hcf with ⟨-, -, -, -, -, -, #Hca, -, -⟩
  unfold ctxErrClientAll; iunfold ctxErrClientAllW at Hca; iexact Hca

/-- **etcd's client is the cache's** (see the file header). -/
theorem isEtcdClient_of_km (cl w api : Loc) (γ : KMNames) (dup : Bool) (pfx : GoString)
    (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗
      clientKVAddr cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
      clientWatcherAddr cl ↦□ GoInterface.ok (watcherIfaceOf w) ∗
      isKv api γ.kv dup ∗ isKvWatcher w γ.kv ∗ kmInv γ ⊢
    isEtcdClient (EM := etcdModelOfKV γ) cl pfx := by
  iintro ⟨#P1, #P2, #P3, #HKV, #HW, #Hkv, #Hw, #Hinv⟩
  ihave #Hall := ctxErrClientAll_of_kvWatcher w γ.kv $$ Hw
  unfold isEtcdClient
  iexists kvIfaceOf api, watcherIfaceOf w
  iframe HKV HW
  isplitr
  · iapply isEtcdKVE_of_km api γ dup pfx hp
    iframe #
  isplitr
  · iapply isEtcdWatcher_of_km w γ pfx hp hff
    iframe #
  iapply isEtcdProgressNotifier_of_km w γ.kv
  iframe #

/-- **A `*kv` of the members at one server's names is a client of its KV** (`isKv`, D44): its
connection's object and the members' registrations, each at the KV's state name, with the
receipts' bound (D48); `dup` (no claim that the members never refuse a request: a reader's). -/
theorem isKv_of_regs [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (api : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (γk : KVNames) (hst : γr.kv.st = γk.st) (hrb : receiptBound GF ≤ 2 ^ 62) :
    kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ⊢ |==> isKv api γk true := by
  iintro ⟨#Ho, #Hr⟩
  imod (srvStart_alloc (GF := GF) (srvsAt addr E γr cid mid)) with #Hs
  imodintro
  iapply (isKv_intro api γk true (srvsAt addr E γr cid mid)
    (fun x hx => by obtain ⟨a, -, rfl⟩ := srvsAt_mem hx; exact hst) (fun h => by cases h) hrb)
  rw [srvsAt_addr]
  iframe #

end proofs

end client
end EtcdGrove
end Perennial
