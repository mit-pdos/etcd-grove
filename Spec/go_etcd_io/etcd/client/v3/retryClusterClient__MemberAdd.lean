/-
`(*clientv3.retryClusterClient).MemberAdd` (`client/v3/retry.go`).

Users: `cluster.*` (through `remoteClusterAt`, `retryClusterHandle_remoteClusterAt`).

Proof sketch: passes the options through to the stub (non-repeatable): `rcc.cc` is `pb.NewClusterClient(c.conn)`, the stub over `connOk` (2a/3h).

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

/-- `r.MemberAdd`: the wire contract at its request. -/
def retryClusterClient.MemberAdd.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (who : Principal) (urls : List GoString) (learner : Bool),
  RemoteCallTriple (fun s => r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryClusterClient.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClusterHandle r γ who) γ who (.memberAdd urls learner)

end spec

end ClientV3
end EtcdGrove
end Perennial
