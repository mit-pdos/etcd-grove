/-
`(*clientv3.cluster).MemberList` (`client/v3/cluster.go`).

Users: `Client.Sync` (the auto-sync: the members' client URLs, `idUpd`'s update), snippet
`clientv3client/cluster.go` (`ReqMemberListLinearizable`); etcdctl.

Proof sketch: `OpGet("", opts...)` (W0's `OpGet.spec`: the `Op` `opGetM [] gs`; it panics on
`WithPrefix` with `WithFromKey`: the premise, as W0's `Get`), reads its `serializable`; the request
`Linearizable: !serializable`; `c.remote.MemberList` (`remoteClusterAt_call`: repeatable, the update
persistent), `ContextError` on an error.

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

/-- `cl.MemberList(ctx, opts...)`: the request `.memberList lin` (`lin`: not
`WithSerializable`), linearized by the caller's persistent update (a serializable list is answered from
a member's view, any list: `clusterStep`), or an error that settles nothing. -/
def cluster.MemberList.spec : Prop :=
  ∀ (cl : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (opts : GoSlice)
    (gs : List (OpM → OpM)),
  ¬ prefixAndFromKey gs →
  CallTriple (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty @!! go!"MemberList")) (Val #ctx)) (Val #opts))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clusterHandle cl γ who ∗ Context.ctxOk ctx ∗ optsAt opts gs) (optsAt opts gs) γ who
    (.memberList (!(opGetM [] gs).serializable)) true ansReply

end spec

end ClientV3
end EtcdGrove
end Perennial
