/-
## `Inflights.reset()` (internal)

**Users.** `Progress.ResetState`. Mirrors the code: the ring emptied.
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

/-- (internal) Empties the ring. -/
def Inflights.reset.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"go.etcd.io/raft/v3/tracker.reset")) (Val #()))
  {{ RET #(); inflightsOwn p { I with items := [] } }}

end spec
end Tracker
end EtcdGrove
end Perennial
