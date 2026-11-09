/-
`(*clientv3.lessor).KeepAliveOnce` (`client/v3/lease.go`).

Users: no user in scope (etcdctl's `lease keep-alive --once`); snippet `clientv3lease/once.go`
(`ReqKeepAliveOnce`).

Proof sketch: a loop over `keepAliveOnce` (its spec): on success, `TTL <= 0` gives
`rpctypes.ErrLeaseNotFound` (rpctypes' law: the variable holds `errVal .leaseNotFound`) with the
reply; on an error, `isHaltErr` (its spec: true for a done context or a status other than
`Unavailable`/`Internal`) returns `ContextError`'s error, else loops (nothing carried but the
handle).

Changes: new (no old spec).

Margin: the response's header is not related to the model.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `l.KeepAliveOnce(ctx, id)`: one keep-alive answered: a positive TTL, or a TTL `≤ 0` with
`ErrLeaseNotFound`, or an error. -/
def lessor.KeepAliveOnce.spec : Prop :=
  ∀ (l : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"KeepAliveOnce")) (Val #ctx)) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ ttl, kaRespOwn resp id ttl ∗ ⌜0 < sint.Z ttl⌝) ∨
      (⌜err = errVal .leaseNotFound⌝ ∗ ∃ ttl, kaRespOwn resp id ttl ∗ ⌜sint.Z ttl ≤ 0⌝) ∨
      (⌜resp = null⌝ ∗ ∃ k, callErr err k) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
