/-
`(*clientv3.cluster).memberAdd` (`client/v3/cluster.go`).

Users: `MemberAdd`, `MemberAddAsLearner`.

Proof sketch: `types.NewURLs(peerAddrs)` (`Types.NewURLs.spec`: an error exactly when not
`urlsValid`: then returns it, the update untouched); builds the `MemberAddRequest` (`reqOwn`), calls
`c.remote.MemberAdd` (`clusterHandle`: `remoteClusterAt`, non-repeatable), `ContextError` on an error.

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

/-- `cl.memberAdd(ctx, urls, learner)`. -/
def cluster.memberAdd.spec : Prop :=
  ∀ (cl : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (sl : GoSlice) (urls : List GoString)
    (learner : Bool),
  CheckedCallTriple (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty @!! go!"memberAdd")) (Val #ctx)) (Val #sl)) (Val #learner))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clusterHandle cl γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ sl ↦*□ urls) iprop(True) γ who (.memberAdd urls learner) false
    (urlsValid urls) ansReply

end spec

end ClientV3
end EtcdGrove
end Perennial
