/-
`(*clientv3.Client).Sync` (`client/v3/client.go`).

Users: `autoSync`; snippet `clientv3client/cluster.go` (`ReqSync`).

Proof sketch: `c.MemberList(ctx)` (the `Cluster` field, `clientCore`: `clusterAt`; linearizable,
`.memberList true`) with the update built from `idUpd γ` (the step changes nothing: a member list is
a read), whose `Q` keeps `etcdLb γ σ` and `res = .ok (.memberList σ.members)`; an error returned. The
client URLs of the named voters (3h's member unfold law): each serves `γ` (2e's law
`memberServes`: a member of a state the cluster has been in that has published serves at its client
URLs); `verify.Verify` (no assertion: `verifyOff`); `SetEndpoints` (its spec); `GetLogger().Debug`.

Changes: new (no old spec).

Margin: an empty list (no member published yet) is set as is (the client then has no endpoint and
its calls fail).
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

/-- `c.Sync(ctx)`: the endpoints replaced by the cluster's members' client URLs, or an error. -/
def Client.Sync.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ verifyOff }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Sync")) (Val #ctx))
  {{ (err : GoInterface), RET #err; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
