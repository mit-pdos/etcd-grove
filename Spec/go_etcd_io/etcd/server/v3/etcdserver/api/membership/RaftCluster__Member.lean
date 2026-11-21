/-
`membership.RaftCluster.Member` (`cluster.go`: under `c`'s mutex, a clone of the member `id`, or
`nil`). Lean-first (no Rocq counterpart); prove-srvloops (2026-11-21): the leader lookup of the
server's `waitLeader`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.Member(id)` (`c` a cluster, at any side condition of its lock invariant,
`isRaftClusterG`) returns `nil` (no member `id`: `c.members[id]` is `nil`, whose `Clone()` is
`nil`) or a fresh member, owned whole with its two URL slices (`Clone`'s copy). -/
abbrev membership.RaftCluster.Member.spec : Prop :=
  ∀ (c : Loc) (RM : membership.RcSide GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterG c RM }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Member")) (Val #id))
  {{ (m : Loc), RET #m; ⌜m = null⌝ ∨
      ∃ (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (pus cus : List GoString),
        m ↦ v ∗ v.RaftAttributes'.PeerURLs' ↦* pus ∗ v.Attributes'.ClientURLs' ↦* cus }}

/-- The static cluster's (`isRaftCluster`, `isRaftCluster_static`). -/
theorem membership.RaftCluster.Member.spec_static (h : membership.RaftCluster.Member.spec (GF := GF) (hG := hG))
    (c : Loc) (id : w64) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Member")) (Val #id))
  {{ (m : Loc), RET #m; ⌜m = null⌝ ∨
      ∃ (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (pus cus : List GoString),
        m ↦ v ∗ v.RaftAttributes'.PeerURLs' ↦* pus ∗ v.Attributes'.ClientURLs' ↦* cus }} := by
  rw [(membership.isRaftCluster_static c).to_eq]
  exact h c _ id

end spec

end EtcdGrove
end Perennial
