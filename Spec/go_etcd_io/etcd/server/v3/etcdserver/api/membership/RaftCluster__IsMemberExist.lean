/-
`membership.RaftCluster.IsMemberExist` (`cluster.go:829-836`: under the lock, `_, ok := c.members[id]`).
Lean-first (no Rocq counterpart); PR #22188 verification.
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

/-- `c.IsMemberExist(id)` (`c` a cluster, `isRaftCluster`) returns whether `id` is in `c.members`
at the lock point (some boolean `b`). -/
abbrev membership.RaftCluster.IsMemberExist.spec : Prop :=
  ∀ (c : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsMemberExist")) (Val #id))
  {{ (b : Bool), RET #b; True }}

/-- Exact specification of `c.IsMemberExist(id)` when `c`'s mutex guards a members map `ms` whose
lookup `(ms !! id).isSome` is `b`: returns `b`. -/
abbrev membership.RaftCluster.IsMemberExist_exact.spec : Prop :=
  ∀ (c : Loc) (id : w64) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      sync.isMutex (membership.rcMutexAddr c)
        iprop(∃ (mp : Loc) (ms : GMap w64 Loc),
          membership.rcMembersAddr c ↦ mp ∗ mp ↦$ ms ∗ ⌜(ms !! id).isSome = b⌝) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsMemberExist")) (Val #id))
  {{ RET #b; True }}

end spec

end EtcdGrove
end Perennial
