/-
## `Progress.MaybeDecrTo(rejected, matchHint)`

**Users.** `stepLeader`'s rejected `MsgAppResp` (`raft.go:1521`): R2.

**Proof sketch.** Field reads and writes. **Changes.** Over the model. **Margin.** None.
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

/-- Moves `Next` back after a rejection (a stale one changes nothing); whether it moved. -/
def Progress.MaybeDecrTo.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (rej hint : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"MaybeDecrTo")) (Val #rej)) (Val #hint))
  {{ RET #(P.maybeDecrTo rej hint).2; progressOwn p (P.maybeDecrTo rej hint).1 }}

end spec
end Tracker
end EtcdGrove
end Perennial
