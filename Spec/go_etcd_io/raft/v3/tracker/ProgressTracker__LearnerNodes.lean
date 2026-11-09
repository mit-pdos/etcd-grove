/-
## `ProgressTracker.LearnerNodes()`

**Users.** None in raft, etcd or the examples (raft's tests). Kept: verified before (PRINCIPLES,
"A smaller API is not a narrower scope").

**Proof sketch.** `nil` for no learner; else a fresh slice by `range`, `slices.Sort`.

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__LearnerNodes.lean`): sorted.

**Margin.** None.
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

/-- The learners, sorted, in a fresh slice (`nil` for none). -/
def ProgressTracker.LearnerNodes.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T ∗ ⌜GMap.size T.conf.learners ≤ Quorum.sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"LearnerNodes")) (Val #()))
  {{ (sl : GoSlice), RET #sl; progressTracker p T ∗ sl ↦* (Quorum.sorted T.conf.learners) }}

end spec
end Tracker
end EtcdGrove
end Perennial
