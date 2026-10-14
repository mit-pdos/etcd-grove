/-
`membership.RaftCluster.Members` (`cluster.go`: under `c`'s mutex, a clone of each member, sorted
by id). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): `isRaftCluster`, and the
result's members.
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

/-- `c.Members()` (`c` a cluster, `isRaftCluster`) returns a slice of fresh members (owned:
clones of the cluster's; their order, by id, is not stated: no caller reads it). -/
abbrev membership.RaftCluster.Members.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ ms : List Loc, membership.membersAt sl ms }}

end spec

end EtcdGrove
end Perennial
