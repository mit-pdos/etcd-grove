/-
`(*clientv3.cluster).MemberRemove` (`client/v3/cluster.go`).

Users: no user in scope (etcdctl); the `Cluster` bundle.

Proof sketch: builds the request, `c.remote.MemberRemove` (`remoteClusterAt_call`, non-repeatable),
`ContextError` on an error.

Changes: new (no old spec).

Margin: none.
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

/-- `cl.MemberRemove(ctx, id)`: the request linearized by the caller's update (exclusive), or an error
that settles nothing. -/
def cluster.MemberRemove.spec : Prop :=
  ∀ (cl : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (id : w64),
  CallTriple (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty @!! go!"MemberRemove")) (Val #ctx)) (Val #id))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clusterHandle cl γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who) iprop(True) γ who (.memberRemove (uint.nat id)) false ansReply

end spec

end ClientV3
end EtcdGrove
end Perennial
