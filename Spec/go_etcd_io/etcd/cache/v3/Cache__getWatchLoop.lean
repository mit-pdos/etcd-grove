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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.getWatchLoop()`, by the demux's writer (`cacheWriter`, any state, with the revision bound)
in a goroutine of the cache's wait group: until the internal context is done, it runs `getWatch`
(a `get` and a `watch`), prints its error (`fmt.Printf`), and waits for the backoff (a timer of
the cache's `Clock`, stopped if the internal context ends first) or the internal context.

The backoff (etcd#22408): the cache's clock is `isClockFor cf.clock (cacheClockOk cf.cfg)`
(`isCacheFields`), so the proof shows that every retry timer is in
`[InitialBackoff, MaxBackoff]`, given `BackoffOk cf.cfg` (`isCacheFields`: `newCache`'s checks and
`CfgBounded`'s `MaxBackoff < 2^62`, without which the doubling wraps, `backoffAt_wraps`). The
exact schedule, `min(InitialBackoff·2^k, MaxBackoff)`, is the proof's loop invariant (`backoffAt`,
`backoffAt_eq_min` in `Proof/.../Cache__getWatchLoop.lean`), not part of this triple. It returns once the internal context is done, with the wait-group token
and the demux's writer, in some state.

The store has several writers: each `watch` iteration's `applyStorage` goroutine may outlive its
iteration and its `watch`, draining its stopped watcher's buffered responses; the store's lock
invariant keeps it certified (`isStoreWriter`, `storeApplyCert`), and every `get`'s `Restore` is
at or above every revision the store can be at: the revision bound (`cacheBound`), which etcd has
reached, so that the client's linearizable get (`isEtcdKV`) returns at least it. -/
abbrev Cache.getWatchLoop.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (c0 : DemuxCore),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheWriter cf γd cap c0 ∗ cacheWgLoopRunning cf }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"getWatchLoop")) (Val #()))
  {{ RET #(); cacheWgLoopRunning cf ∗ ∃ c1 : DemuxCore, cacheWriter cf γd cap c1 }}

end spec

end EtcdGrove
end Perennial
