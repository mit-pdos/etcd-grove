/-
`New(lg, b, le, cfg)` (`watchable_store.go`): the watchable store over the storage `b`, its two
loops started.

**Users.** `NewServer` (`etcdserver/server.go:366`, 2e: `mvcc.New(srv.Logger(), srv.be, srv.lessor,
mvccStoreConfig)`); this repository's mvcc examples. Snippet: `mvccwatch/store.go` `ReqStoreWrites`.

**Proof sketch.** `newWatchableStore` (its spec: `NewStore`'s, 3e's, the store's views and the
lessor's range deleter set to the watchable store's `Write`, the watch invariant allocated, the
loops' starting shares, each with a reader of the store kept out of the client's tokens);
`s.wg.Add(2)` (Perennial's wait group, backed by the two goroutines: their deposits at `Done` are
the loops' readers, which `Close` takes back after `Wait`); `go s.syncWatchersLoop()`, `go
s.syncVictimsLoop()` (each with its loop share; a fork needs no token).

**Changes** from `specs-ref`'s `New.lean`: over 3e's constructor slots (`storeBoot`/`storeBooted`,
provisional) in place of the backend's and lessor's internal resources and the receipt bound; the
result is the handle (`watchableAt`, with 3e's `isMvcc`), the client-owned state at the storage's
history, the open token.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch

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

/-- **`New(lg, b, le, cfg)`**: a watchable store of fresh names `γ`, at the storage's history `h`
(nothing pending), its loops running; with what 3e's `NewStore` gives. -/
def New.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (h : KVHist),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ storeBoot lg b le cfg h }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg)) (Val #b))
      (Val #le)) (Val #cfg))
  {{ (kv : GoInterface), RET #kv; ∃ γ : MvccName,
      watchableAt kv γ ∗ mvccState γ { kv := h, pending := [] } ∗ mvccOpen γ ∗ storeBooted kv γ le }}

end spec

end Mvcc
end EtcdGrove
end Perennial
