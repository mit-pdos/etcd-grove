/-
`(*EtcdServer).NextRequestID()` (`interface.go:34-36`): `s.reqIDGen.Next()`.

**Users**: the read loop (`readEnv`'s `NextRequestID` row: each read round's context).

**Proof sketch**: the read-only field `s.reqIDGen` (`srvNode`: 2c's `IdUtil.idGen` over the
member's id space `srvIdSpace s γi`); `Generator.Next.spec`.

**Changes**: verify round (A7-provability F4): new here (the old tree's
`EtcdServer__NextRequestID.lean`).

**Margin**: none (the id space's freshness across restarts is `idutil`'s recorded scope,
`nonissues/etcd-request-id-restart-reuse.md`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`NextRequestID()`**: a fresh id of the member's id space. -/
def EtcdServer.NextRequestID.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (γi : IdUtil.IdSpace),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvIdSpace s γi }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"NextRequestID")) (Val #()))
  {{ (rid : w64), RET #rid; IdUtil.idFresh γi rid }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
