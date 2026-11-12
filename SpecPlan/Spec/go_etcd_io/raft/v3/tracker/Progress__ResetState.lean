/-
## `Progress.ResetState(state)`

**Users.** `BecomeProbe`, `BecomeReplicate`, `BecomeSnapshot` (each with its state). Snippet
`raftconf/tracker.go` (`ReqProgressFlow`, through them).

**Proof sketch.** Three field writes; `Inflights.reset`. **Changes** (from `specs-ref`'s
`tracker/Progress__ResetState.lean`): the state as the model's `PrState` (Go's `StateType` values).
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

/-- Enters state `st`: unpaused, no pending snapshot, the ring emptied. -/
def Progress.ResetState.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (st : PrState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"ResetState")) (Val #(st.code)))
  {{ RET #(); progressOwn p (P.resetState st) }}

end spec
end Tracker
end EtcdGrove
end Perennial
