/-
## `outgoingPtr(voters)` (internal)

**Users.** `EnterJoint`, `LeaveJoint`. Mirrors the code: the second element's address.
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

/-- (internal) The address of the outgoing half. -/
def outgoingPtr.spec : Prop :=
  ∀ (vp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange }}
    (App (Val #(functions go_etcd_io.raft.v3.confchange.outgoingPtr [])) (Val #vp))
  {{ RET #(arrayIndexRef GoMap 1 vp); True }}

end spec
end ConfChange
end EtcdGrove
end Perennial
