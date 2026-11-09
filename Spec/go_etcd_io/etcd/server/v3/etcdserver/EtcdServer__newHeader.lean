/-
## `(*EtcdServer).newHeader()` (internal helper)

Users: `LeaseLeases` (`v3_server.go:748`). Mirrors the code: a fresh `ResponseHeader` from the
cluster id, the member id, `KV().Rev()`, `Term()`, `Leader()`. Changes: the old spec gave the ids
(`srvHeaderFacts`), which leaked into the lease handlers' specs (`lease-grpc.md`); now only an owned
header. Margin: its values are not stated (2a's `fill` overwrites the ids; no caller reads the
revision).
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

/-- A fresh header, owned. -/
def EtcdServer.newHeader.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; threadTok ∗ ∃ m, respHeaderOwn h (DFrac.own 1) m }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
