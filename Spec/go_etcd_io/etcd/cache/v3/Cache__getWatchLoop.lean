/-
`Cache.getWatchLoop()` (`cache/cache.go`): the cache's watch loop, run by `newCache`'s goroutine.
Lean-first (no Rocq counterpart); see `InvCache.lean` and `InvEtcd.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.getWatchLoop()`, with the demux's writer and the store's writer (any states): until the
internal context is done, it runs `getWatch` (a `get` and a `watch`), prints its error
(`fmt.Printf`), and waits for the backoff (`time.After`) or the internal context. It returns once
the internal context is done, with both writers, in some states.

This is the proof that the store has one writer: the writer's token (`storeWriter`) threads
through the loop, `get`'s `Restore`, `watch`, and each iteration's `applyStorage` goroutine, which
hands it back through `applyErr` before the loop goes on (`Cache.watch`'s spec).

Every `get` needs etcd's linearizability for the store's latest revision: the writer knows etcd
has reached it (`etcdReached`, the store's revision certificate), and the client's get is
linearizable (`isEtcdKV`). -/
abbrev Cache.getWatchLoop.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (c0 : DemuxCore) (st : StoreState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheWriter cf γd cap c0 ∗
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached st }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"getWatchLoop")) (Val #()))
  {{ RET #(); ∃ (c1 : DemuxCore) (st' : StoreState), cacheWriter cf γd cap c1 ∗
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached st' }}

end spec

end EtcdGrove
end Perennial
