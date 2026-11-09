/-
## `ProgressTracker.VoterNodes()`

**Users.** `newRaft`'s log line (`raft.go:490`): R2. (etcd and the examples read `Status` instead.)

**Proof sketch.** `JointConfig.IDs` (`configOwn_open`); a fresh slice appended by `range`;
`slices.Sort` (`≤ 2^62`).

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__VoterNodes.lean`): sorted (was a
permutation), both halves (was the simple configuration's voters).

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

/-- Both halves' voters, sorted, in a fresh slice. -/
def ProgressTracker.VoterNodes.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T ∗ ⌜GMap.size (T.conf.voters ∪ T.conf.votersOutgoing) ≤ Quorum.sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"VoterNodes")) (Val #()))
  {{ (sl : GoSlice), RET #sl; progressTracker p T ∗
      sl ↦* (Quorum.sorted (T.conf.voters ∪ T.conf.votersOutgoing)) }}

end spec
end Tracker
end EtcdGrove
end Perennial
