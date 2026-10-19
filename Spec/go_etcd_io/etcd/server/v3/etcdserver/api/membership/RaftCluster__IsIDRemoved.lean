/-
`membership.RaftCluster.IsIDRemoved` (`cluster.go:181-185`: under the lock, `c.removed[id]`).
Lean-first (no Rocq counterpart); D21 M2 (2026-10-19): `EtcdServer.Process`'s check of the sender.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.IsIDRemoved(id)` (`c` a cluster, `isRaftCluster`) returns `false`: the cluster's removed
map is empty (`rcLockInv`: static membership). -/
abbrev membership.RaftCluster.IsIDRemoved.spec : Prop :=
  ∀ (c : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsIDRemoved")) (Val #id))
  {{ RET #false; True }}

end spec

end EtcdGrove
end Perennial
