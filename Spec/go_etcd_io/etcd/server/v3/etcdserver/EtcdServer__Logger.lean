/-
## `(*EtcdServer).Logger()` (`server.go:444-449`)

**Users.** Most of the server's methods; v3rpc's handlers.

**Proof sketch.** `lgMu`'s read lock (`srvMember`'s realization: the logger field under it, a zap
logger, `cfg.Logger`).

**Changes** (from `specs-ref`'s `EtcdServer__Logger.lean`, a reader slot of `lgMu`): no slot (the
bounds plan: the lock's owner keeps the readers).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_uber_org.zap.Api

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

/-- **`Logger()`**: the server's zap logger. -/
def EtcdServer.Logger.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Logger")) (Val #()))
  {{ (lg : Loc), RET #lg; Zap.isLogger lg ∗ threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
