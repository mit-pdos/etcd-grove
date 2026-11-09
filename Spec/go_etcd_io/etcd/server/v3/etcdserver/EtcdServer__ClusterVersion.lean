/-
`(*EtcdServer).ClusterVersion()` (`server.go:2215-2220`): `nil` without a cluster, else
`s.cluster.Version()`.

**Users**: `start` (logging), v3rpc's `maintenanceServer.Status` and `Downgrade` (through the
version adapter), etcdhttp's version handler.

**Proof sketch**: the read-only `s.cluster` (`srvMember`'s realization: 2e's membership view);
2e's `RaftCluster.Version` (its read lock: the caller's `threadTok`; a copy of the version or
`nil`: requested of server-boot, A8-completeness F3).

**Changes**: verify round (A7-completeness F3, A8-completeness F5): new here (the old tree's
`EtcdServer__ClusterVersion.lean`).

**Margin**: nothing is said of the version (a status report); a caller that reads it
(`v.String()`) needs 2e's `RaftCluster.Version` contract, requested.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **`ClusterVersion()`**: the cluster's version, or `nil`. -/
def EtcdServer.ClusterVersion.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗
      threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"ClusterVersion")) (Val #()))
  {{ (v : Loc), RET #v; threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
