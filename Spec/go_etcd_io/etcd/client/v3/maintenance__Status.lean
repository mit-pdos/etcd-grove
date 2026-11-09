/-
`(*clientv3.maintenance).Status` (`client/v3/maintenance.go`).

Users: Kubernetes' feature checker (`feature_support_checker.go`: the member's `Version`) and storage
prober (`etcd3.go`: `DbSize`), `Client.checkVersion` (`RejectOldCluster`); snippet
`clientv3client/maint.go` (`ReqStatus`).

Proof sketch: `m.dial(endpoint)` (the closure `NewMaintenance` built: `c.Dial(endpoint)`, a new
connection with the client's interceptors (`Client.Dial.spec`), or a wrapped error), deferred
`cancel` (closes it); `remote.Status(ctx, &pb.StatusRequest{}, m.callOpts...)` (the stub: a fresh
reply or a classified error, 2a); `ContextError` on an error.

Changes: new (no old spec).

Margin: the reply's fields are not related to the model (a member's local view: version, sizes,
leader, raft indices): the caller learns only that it got one.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `mt.Status(ctx, ep)`: the member's status reply (owned), or an error. -/
def maintenance.Status.spec : Prop :=
  ∀ (mt : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (ep : GoString),
  {{ iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ maintHandle mt γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who) }}
    (App (App (Val (mt @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty @!! go!"Status")) (Val #ctx)) (Val #ep))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ statusRespOwn resp) ∨ ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
