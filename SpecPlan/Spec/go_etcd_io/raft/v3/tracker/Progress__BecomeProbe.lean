/-
## `Progress.BecomeProbe()`

**Users.** `stepLeader` (`raft.go:1524`, `1559`, `1631`, `1637`, `1648`: a rejected append, a
snapshot done or failed, an unreachable peer): R2. Snippet `raftconf/tracker.go`
(`ReqProgressFlow`).

**Proof sketch.** `ResetState(StateProbe)`; `Next` from the match (or past the pending snapshot);
`sentCommit` capped. **Changes.** Over the model. **Margin.** None.
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

/-- Probes the peer (from its match, or past a pending snapshot). -/
def Progress.BecomeProbe.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"BecomeProbe")) (Val #()))
  {{ RET #(); progressOwn p P.becomeProbe }}

end spec
end Tracker
end EtcdGrove
end Perennial
