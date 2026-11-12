/-
## `ProgressTracker.RecordVote(id, v)`

**Users.** `raft.poll` (`raft.go:1099`: a vote response, or the candidate's own vote): R2. Snippet
`raftconf/tracker.go` (`ReqTallyVotes`).

**Proof sketch.** A lookup; an insert if absent. **Changes.** Over `progressTracker`. **Margin.**
None.
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

/-- Records `id`'s vote `v`, unless it already voted. -/
def ProgressTracker.RecordVote.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV) (id : w64) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"RecordVote")) (Val #id)) (Val #v))
  {{ RET #(); progressTracker p { T with votes := if id ∈ T.votes then T.votes else <[id := v]> T.votes } }}

end spec
end Tracker
end EtcdGrove
end Perennial
