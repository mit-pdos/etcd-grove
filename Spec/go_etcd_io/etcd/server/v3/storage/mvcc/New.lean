/-
`New(lg, b, le, cfg)` (`watchable_store.go`): the watchable store over the storage `b`, its two
loops started: `NewStore`'s contract (3e's `NewStore.spec`) with the watchable store as the handle.

**Users.** `NewServer` (`etcdserver/server.go:366`, 2e: `mvcc.New(srv.Logger(), srv.be, srv.lessor,
mvccStoreConfig)`); this repository's mvcc examples. Snippet: `mvccwatch/store.go` `ReqStoreWrites`.

**Proof sketch.** `newWatchableStore` (its spec: `NewStore`'s post, `mvccRevLent γ 0 ∗
mvccRestoreGate γ 1` included, the store's views and the lessor's range deleter set to the watchable
store's `Write` (`mvccDeleter`: `KV.Write.contract` at `*watchableStore`), the watch invariant
allocated (`mvccLb`'s authority at `h`: part of `mvccState`'s realization, `req/`), the loops'
shares); `s.wg.Add(2)` (Perennial's wait group, backed by the two goroutines: their deposits at
`Done` are the loops' shares, which `Close` takes back after `Wait`); `go s.syncWatchersLoop()`, `go
s.syncVictimsLoop()` (each with its share; a fork needs no token). The loops' storage reads use two
of the store's own reader slots (3e's `mvccOwnN`, `mvccReaderN_eq`: not among the client's
`mvccTokN`), borrowed per pass from the store's current storage (so that `Restore` can give the old
storage's `storageRest B mvccReaderN` back while the loops keep running): the hand-off is 3e's
internal law, requested of 3e at integration (I6).

**Changes** from `specs-ref`'s `New.lean`: 3e's restated `NewStore` contract (any image of a history,
the leases re-attached, the hook at any share) with `watchableAt` for the handle; the receipt bound
as `NewStore`'s. (Integration: no `MvccReachable` premise, `mvccRevLent γ 0 ∗ mvccRestoreGate γ 1`
given, following 3e's round-1 `NewStore`.)

**Margin.** As `NewStore`'s.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`New(lg, b, le, cfg)`**: `NewStore`'s result (3e's `NewStore.spec`) as a watchable store
(`watchableAt`), its loops running. -/
def New.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : Loc) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (h : EtcdModel.KVHist) (u : Bool) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat)
    (ls : Lease.LessorState) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ ⌜storeCfgOk cfg⌝ ∗
      mvccStorageFor B Pk h u ∗
      storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y ∗
      Lease.isLessor le γl c ∗ Lease.lessorState γl n ls }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(GoInterface.ok (storageVal B)))) (Val #(Lease.lessorIface le))) (Val #cfg))
  {{ (kv : GoInterface), RET #kv; ∃ γ : MvccName, watchableAt kv γ ∗ mvccLessorIs γ γl ∗
      mvccState γ ⟨h, []⟩ ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccTokN ∗
      mvccRevLent γ 0 ∗ mvccRestoreGate γ 1 ∗
      storageHook B dq f ∗ (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      (∃ (rd : GoFunc) (n' : Nat) (ls' : Lease.LessorState), mvccDeleter rd γ ∗
        ⌜RestoreLs { ls with rd := rd } h.store ls'⌝ ∗ Lease.lessorState γl n' ls') }}

end spec

end Mvcc
end EtcdGrove
end Perennial
