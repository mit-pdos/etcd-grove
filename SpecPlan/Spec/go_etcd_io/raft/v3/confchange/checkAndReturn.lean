/-
## `checkAndReturn(cfg, trk)` (internal)

**Users.** `checkAndCopy`, `Simple`, `EnterJoint`, `LeaveJoint`. Mirrors the code: the inputs if
`checkInvariants` accepts them (the model's `checked`).
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

/-- (internal) The working copy, if `checkInvariants` accepts it. -/
def checkAndReturn.spec : Prop :=
  ∀ (B : Base) (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (m : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ccState B cfg trk m }}
    (App (App (Val #(functions go_etcd_io.raft.v3.confchange.checkAndReturn [])) (Val #cfg)) (Val #trk))
  {{ (cfg' : go_etcd_io.raft.v3.tracker.Config) (trk' : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg' #trk') #err); ccState B cfg trk m ∗
      ⌜if m.CfgOk then err = interface.nil ∧ cfg' = cfg ∧ trk' = trk else err ≠ interface.nil⌝ }}

end spec
end ConfChange
end EtcdGrove
end Perennial
