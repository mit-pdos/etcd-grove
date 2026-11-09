/-
## `(*EtcdServer).Watchable()`

**Users.** The gRPC watch server (`api/v3rpc/watch.go`, `NewWatchServer`: `s.Watchable()`, 2b).
Snippet: none of its own (2b's watch snippets go through it).

**Proof sketch.** `s.KV()` (`s.kv`, read-only after `start`: `isServer`'s), as a `WatchableKV`.

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Watchable.lean`, the watch slice's W-S) restated
over the provisional slot `srvWatchable` (3f's watchable store at the member's applied history,
2d's), requested in `req/`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The member's watchable store. -/
def EtcdServer.Watchable.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Watchable")) (Val #()))
  {{ (w : GoInterface), RET #w; srvWatchable s γ w }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
