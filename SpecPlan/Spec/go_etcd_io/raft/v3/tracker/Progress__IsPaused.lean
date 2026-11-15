/-
## `Progress.IsPaused()`

**Users.** `maybeSendAppend` (`raft.go:620`): R2. Snippet `raftconf/tracker.go`
(`ReqProgressFlow`).

**Proof sketch.** A switch on `State` (one of the three: `progressOwn`'s `PrState`; Go panics
"unexpected state" on another value, which `progressOwn` excludes). **Changes.** Over the model.
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

/-- Whether sending appends to the peer is paused (always in snapshot state). -/
def Progress.IsPaused.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"IsPaused")) (Val #()))
  {{ RET #P.isPaused; progressOwn p P }}

end spec
end Tracker
end EtcdGrove
end Perennial
