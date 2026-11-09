/-
## `ProgressTracker.ResetVotes()`

**Users.** `reset` (`raft.go:812`, every new term), `becomePreCandidate` (`raft.go:944`): R2.

**Proof sketch.** A fresh map stored in `p.Votes`. **Changes.** Over `progressTracker`.
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

/-- Forgets the votes. -/
def ProgressTracker.ResetVotes.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"ResetVotes")) (Val #()))
  {{ RET #(); progressTracker p { T with votes := ∅ } }}

end spec
end Tracker
end EtcdGrove
end Perennial
