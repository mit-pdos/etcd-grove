/-
## `ProgressTracker.QuorumActive()`

**Users.** `stepLeader`'s `MsgCheckQuorum` (`raft.go:1300`: a leader that has not heard from a
quorum steps down): R2 (liveness only; safety does not depend on it).

**Proof sketch.** A fresh votes map; `Visit` (the field and map at a share, `I` the votes map so
far: each non-learner's `RecentActive`); `JointConfig.VoteResult` (`configOwn_open`): won iff the
active voters are a joint quorum.

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__QuorumActive.lean`): the result as a
quorum of `activeIds` (was spelled with the tracker's record).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- Whether the recently active voters are a joint quorum. -/
def ProgressTracker.QuorumActive.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T ∗ ⌜GMap.size T.prs ≤ Quorum.sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"QuorumActive")) (Val #()))
  {{ RET #(decide (T.conf.quorum (activeIds T.pv))); progressTracker p T }}

end spec
end Tracker
end EtcdGrove
end Perennial
