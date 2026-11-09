/-
## `(*EtcdServer).StopNotify()` (`server.go:1379`): names only

**Users.** The integration framework's member removal (`cluster.go:362`), `etcdmain`, embed;
`ReqStopAfterError`. **Why it is true.** The field `start` set. **Changes**: new (round 1,
completeness F3). **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **The channel closed when the server's stop is over.** -/
def EtcdServer.StopNotify.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"StopNotify")) (Val #()))
  {{ (ch : Loc), RET #ch; doneCh s ch }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
