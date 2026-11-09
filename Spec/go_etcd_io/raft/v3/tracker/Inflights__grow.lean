/-
## `Inflights.grow()` (internal)

**Users.** `Add`. Doubles the buffer (at most to `size`), copying it; the model does not change. Only
when the ring is not full (Go would otherwise grow a zero-capacity ring past its size).
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

/-- (internal) A larger buffer, the same messages. -/
def Inflights.grow.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I ∗ ⌜I.full = false⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"go.etcd.io/raft/v3/tracker.grow")) (Val #()))
  {{ RET #(); inflightsOwn p I }}

end spec
end Tracker
end EtcdGrove
end Perennial
