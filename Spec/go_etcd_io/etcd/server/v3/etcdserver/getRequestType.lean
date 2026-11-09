/-
## `etcdserver.getRequestType(r)` (internal helper)

Users: `processInternalRaftRequestOnce` (`v3_server.go:1087`: the metrics' label). Mirrors the code:
a `switch` on the request's fields (reads only). Changes: unchanged in content. Margin: the label is
not stated (no caller reads it but the metrics).
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

/-- A label (unspecified). -/
def getRequestType.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (ir : IrrBody),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ irrOwn r dq ir }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.getRequestType)) (Val #r))
  {{ (l : GoString), RET #l; irrOwn r dq ir }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
