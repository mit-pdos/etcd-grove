/-
`Cache.watchEvents` (`cache/*.go`), an internal helper.
Users: `Cache.watch`.
Proof sketch: the client's `Watch` of the prefix from `rev` (1b's `watcherAt`: progress and created notifications; each response a fact from the watch's position, `req/go_etcd_io_etcd_client_v3.md`), a loop `select`ing on the cache's context, the watch channel and `applyErr`: `readyOnce.Do(ready.Set)`, an error resets readiness (`ready.Reset.spec`), else `storeCeil_raise` to the response's revisions, `demux.Broadcast.spec`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.watchEvents(rev, applyErr, readyOnce)` while the upstream watch from `rev` runs: returns with the run's role back. -/
def Cache.watchEvents.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (rev : w64) (aec ro : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheLoopRun c (sint.Z rev) ∗ applyErrChan aec ∗ readyOnceAt c ro }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"watchEvents")) (Val #rev)) (Val #aec)) (Val #ro))
  {{ (err : GoInterface), RET #err; cacheLoopRun c (sint.Z rev) }}

end spec

end Cache
end EtcdGrove
end Perennial
