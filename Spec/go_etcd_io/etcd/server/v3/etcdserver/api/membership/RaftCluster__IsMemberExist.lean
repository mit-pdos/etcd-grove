/-
`membership.RaftCluster.IsMemberExist` (`cluster.go`: under the lock, whether the members map
has an entry for `id`). Lean-first (no Rocq counterpart); 2026-10-26: the server's
`IsMemberExist`, the interceptors' check.
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

/-- `c.IsMemberExist(id)` (`c` a cluster, `isRaftCluster`) returns some boolean (whether the
members map has an entry for `id`). -/
abbrev membership.RaftCluster.IsMemberExist.spec : Prop :=
  ∀ (c : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsMemberExist")) (Val #id))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
