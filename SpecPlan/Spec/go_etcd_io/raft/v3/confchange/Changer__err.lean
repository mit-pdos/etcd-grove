/-
## `Changer.err(err)` (internal)

**Users.** `Simple`, `EnterJoint`, `LeaveJoint`. Mirrors the code: zero values and the error.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.confchange.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- (internal) The zero configuration, a `nil` map, and `e`. -/
def Changer.err.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"go.etcd.io/raft/v3/confchange.err")) (Val #e))
  {{ RET (PairV (PairV #(zero_val go_etcd_io.raft.v3.tracker.Config) #map.nil) #e);
      p ↦{dqp} chg }}

end spec
end ConfChange
end EtcdGrove
end Perennial
