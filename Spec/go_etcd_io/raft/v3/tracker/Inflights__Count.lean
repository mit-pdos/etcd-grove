/-
## `Inflights.Count()`

**Users.** `Progress.String` (logging) and raft's tests. Kept: verified before.

**Proof sketch.** A field read. **Changes.** Over the model. **Margin.** None.
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

/-- The number of messages in flight. -/
def Inflights.Count.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"Count")) (Val #()))
  {{ RET #(W64 I.items.length); inflightsOwn p I }}

end spec
end Tracker
end EtcdGrove
end Perennial
