/-
## `(*EtcdServer).Logger()` (`server.go:444-449`)

**Users.** Most of the server's methods; v3rpc's handlers.

**Proof sketch.** `lgMu`'s read lock (`srvFields`' realization: the logger field under it, a zap
logger, `cfg.Logger`).

**Changes** (from `specs-ref`'s `EtcdServer__Logger.lean`, a reader slot of `lgMu`): no slot (the
bounds plan: the lock's owner keeps the readers).

**Margin.** None.
Changes: re-review (RR2): over 2e's `srvFields` (the server literal's read-only fields), not `srvMember`: callable before the transport is set (`NewServer`'s own calls, `Process` from `tr.Start()` on, `start`); a caller holding `srvMember` uses `srvMember_fields`, one holding 2d's `srvNode` `srvNode_fields`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_uber_org.zap.Api

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvFields s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Logger")) (Val #()))
  {{ (lg : Loc), RET #lg; Zap.isLogger lg ∗ threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
