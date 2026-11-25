/-
`membership.RaftCluster.PromoteMember(id, shouldApplyV3)` (`cluster.go`): under the lock, the learner
metric if `id` is the local member; with `shouldApplyV3`, the member's `IsLearner` cleared, the
metric, the backend's member save and a log line; without, a log line. Lean-first (no Rocq
counterpart); route B (2026-11-25): only without `shouldApplyV3`, the call `applyConfChange` makes on a
replayed promotion (one at or below the consistent index at a restart).
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

/-- `c.PromoteMember(id, false)` on a cluster at any side condition `RM` (route B, 2026-11-25): it
takes the cluster's lock, sets the `is_learner` gauge to `0` if `id` is the local member
(`c.localID`), logs a line and gives the lock back with what it guards unchanged (Go, at the etcd pin
`6b942d23f`: `api/membership/cluster.go:498-532`; without `shouldApplyV3` the members map and the
backend are not touched). Its other reads are of read-only fields: the logger (a zap logger), the
cluster id. The `shouldApplyV3` case (the member's `IsLearner` cleared and saved) is not specified:
the server's policy admits a promotion only where its validation fails (`ccValidM`), so
`applyConfChange` never calls it with `shouldApplyV3`. -/
abbrev membership.RaftCluster.PromoteMember.spec : Prop :=
  ∀ (c : Loc) (RM : membership.RcSide GF) (id : w64) (lg : Loc) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterG c RM ∗
      membership.rcLgAddr c ↦□ lg ∗ zapLoggerOk lg ∗ membership.rcCidAddr c ↦□ cid }}
    (App (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"PromoteMember")) (Val #id)) (Val #false))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
