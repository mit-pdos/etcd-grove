/-
`(*EtcdServer).RequestTimeout()` (`interface.go:38-40`): `s.Cfg.ReqTimeout()`.

**Users**: the read loop (`readEnv`'s `RequestTimeout` row), `ensureLeadership`.

**Proof sketch**: the read-only `s.Cfg` (`srvMember`'s realization); `ServerConfig.ReqTimeout`
(arithmetic on two configuration fields: `5s + 2 * ElectionTicks * TickMs ms`, wrapping
`time.Duration` arithmetic, no panic).

**Changes**: verify round (A7-provability F4): new here (the old tree's
`EtcdServer__RequestTimeout.lean`).

**Margin**: the duration is any value.
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

/-- **`RequestTimeout()`**: a duration. -/
def EtcdServer.RequestTimeout.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"RequestTimeout")) (Val #()))
  {{ (d : w64), RET #d; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
