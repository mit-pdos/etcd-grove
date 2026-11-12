/-
## `Inflights.Clone()`

**Users.** `getProgressCopy` (`status.go:48`): R2/R1's `Status`.

**Proof sketch.** A struct copy, the buffer appended to a `nil` slice (fresh).

**Changes.** Over `inflightsOwn`. **Margin.** None.
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

/-- A fresh ring holding the same messages. -/
def Inflights.Clone.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"Clone")) (Val #()))
  {{ (p' : Loc), RET #p'; inflightsOwn p I ∗ inflightsOwn p' I }}

end spec
end Tracker
end EtcdGrove
end Perennial
