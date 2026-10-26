/-
`membership.RaftCluster.IsLocalMemberLearner` (`cluster.go`: under the lock, the local member's
`IsLearner`, or `false` if the local member is not in the members map). Lean-first (no Rocq
counterpart); D43 M4 (2026-10-26): the fork's fix (`goose-lean-learnerfix`,
`issues/etcd-unary-interceptor-learner-removed.md`): no panic for a removed local member.
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

/-- `c.IsLocalMemberLearner()` (`c` a cluster, `isRaftClusterG`, at any side condition: the local
member need not be in the map) returns some boolean. -/
abbrev membership.RaftCluster.IsLocalMemberLearner.spec : Prop :=
  ∀ (c : Loc) (RM : membership.RcSide GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterG c RM }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"IsLocalMemberLearner")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
