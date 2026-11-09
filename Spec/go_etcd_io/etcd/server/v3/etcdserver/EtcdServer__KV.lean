/-
## `(*EtcdServer).KV()` (`server.go:2415`): translated

**Users.** 2a's maintenance (`KV().Rev()`, hashes), the watch server. **Proof sketch.** The
read-only field: 2c's `srvWatchable` (the request path's realization). **Changes**: from
`specs-ref`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's watchable store.** -/
def EtcdServer.KV.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"KV")) (Val #()))
  {{ (w : GoInterface), RET #w; srvWatchable s γ w }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
