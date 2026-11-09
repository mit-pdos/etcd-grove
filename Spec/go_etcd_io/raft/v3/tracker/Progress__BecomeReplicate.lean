/-
## `Progress.BecomeReplicate()`

**Users.** `becomeLeader` (`raft.go:966`, the leader's own progress), `stepLeader` (`raft.go:1545`,
`1560`: a probe answered, a snapshot caught up): R2. Snippet `raftconf/tracker.go`
(`ReqProgressFlow`).

**Proof sketch.** `ResetState(StateReplicate)`; `Next = Match + 1`. **Changes.** Over the model.
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

/-- Replicates to the peer from its match. -/
def Progress.BecomeReplicate.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"BecomeReplicate")) (Val #()))
  {{ RET #(); progressOwn p P.becomeReplicate }}

end spec
end Tracker
end EtcdGrove
end Perennial
