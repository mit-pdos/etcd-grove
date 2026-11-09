/-
## `ProgressTracker.IsSingleton()`

**Users.** `stepLeader`'s read index (`raft.go:2153`, the single-voter shortcut, with the fork's fix
`issues/raft-readindex-singleton-stale.md`): R2.

**Proof sketch.** `configOwn_open`; the two `len`s.

**Changes.** Over `progressTracker` (was `ownTrackerC`). **Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

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

/-- Exactly one voter, not joint. -/
def ProgressTracker.IsSingleton.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"IsSingleton")) (Val #()))
  {{ RET #(decide (GMap.size T.conf.voters = 1 ∧ T.conf.votersOutgoing = ∅)); progressTracker p T }}

end spec
end Tracker
end EtcdGrove
end Perennial
