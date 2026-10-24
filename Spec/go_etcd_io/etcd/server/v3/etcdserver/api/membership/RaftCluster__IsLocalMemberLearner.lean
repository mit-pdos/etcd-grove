/-
`membership.RaftCluster.IsLocalMemberLearner` (`cluster.go:786-805`).
Lean-first (no Rocq counterpart); PR #22188 verification:
when `c.members` has no entry for `c.localID` (`!ok`), logs at `Debug` and returns `false`
instead of calling `c.lg.Panic`.
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

/-- `c.IsLocalMemberLearner()` (`c` a cluster, `isRaftCluster`, whose `rcLocalIn` does not require
`c.localID` to be present in `c.members`) returns whether the local member is a learner (`false` if
`c.localID` has been removed from `c.members`), without panicking. -/
abbrev membership.RaftCluster.IsLocalMemberLearner.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsLocalMemberLearner")) (Val #()))
  {{ (b : Bool), RET #b; True }}

/-- Exact specification of `c.IsLocalMemberLearner()` when the local member `lid` is absent from
`c.members` (`ms !! lid = none`, e.g. after concurrent removal via `ConfChangeRemoveNode`): logs at
`Debug` and returns `false` without panicking. -/
abbrev membership.RaftCluster.IsLocalMemberLearner_absent.spec : Prop :=
  ∀ (c : Loc) (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      sync.isMutex (membership.rcMutexAddr c)
        iprop(∃ (mp lg : Loc) (ms : GMap w64 Loc) (cid : w64),
          membership.rcMembersAddr c ↦ mp ∗ mp ↦$ ms ∗
          membership.rcLocalIDAddr c ↦□ lid ∗
          membership.rcCidAddr c ↦□ cid ∗
          membership.rcLgAddr c ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ ⌜ms !! lid = none⌝) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsLocalMemberLearner")) (Val #()))
  {{ RET #false; True }}

/-- Exact specification of `c.IsLocalMemberLearner()` when the local member `lid` is present in
`c.members` (`ms !! lid = some m`) with `m.IsLearner = il`: returns `il` (`true` for a learner,
`false` for a voting member). -/
abbrev membership.RaftCluster.IsLocalMemberLearner_present.spec : Prop :=
  ∀ (c : Loc) (lid : w64) (il : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      sync.isMutex (membership.rcMutexAddr c)
        iprop(∃ (mp m : Loc) (ms : GMap w64 Loc),
          membership.rcMembersAddr c ↦ mp ∗ mp ↦$ ms ∗
          membership.rcLocalIDAddr c ↦□ lid ∗
          membership.mIsLearnerAddr m ↦ il ∗ ⌜m ≠ null⌝ ∗ ⌜ms !! lid = some m⌝) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsLocalMemberLearner")) (Val #()))
  {{ RET #il; True }}

end spec

end EtcdGrove
end Perennial
