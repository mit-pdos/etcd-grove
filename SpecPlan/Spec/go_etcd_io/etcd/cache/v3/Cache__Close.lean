/-
`(*Cache).Close()` (`cache/cache.go`): cancel the cache's context, wait for its goroutines.

Users: etcd's integration tests (`defer c.Close()`, `t.Cleanup(c.Close)`); `cachekv.go` does not
close its cache. Snippet: `cache/lifecycle.go` `ReqClose`.

Proof sketch: `c.stop()` (Perennial's cancel function: the cache's context done); `c.waitGroup.Wait()`
with the whole `cacheOpen` token: no `Watch` is between its `Add` and its goroutine's start (the
fractions are all here), so `Wait` runs under the wait group's protocol (each goroutine's thread token
given back at its `Done`). The token is given back: a `Watch` after `Close` returned is allowed (Go
allows a wait group's reuse after `Wait` returned; the new goroutine sees the context done and exits).

Changes: from `specs-ref`'s `Cache__Close.lean`: the client-facing `cacheOpen c 1` instead of the
internal handles; the token given back (the old spec consumed it).

Margin: after `Close`, every goroutine of the cache has returned, so every watch channel is closed
and no further event comes: not stated (a consumer's `cacheWatchAt` says only that a channel may
close at any time).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`c.Close()`**, by the holder of the whole `cacheOpen` token (given back). -/
def Cache.Close.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheOpen c 1 }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"Close")) (Val #()))
  {{ RET #(); cacheOpen c 1 }}

end spec

end Cache
end EtcdGrove
end Perennial
