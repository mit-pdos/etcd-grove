/-
## `Changer.checkAndCopy()` (internal)

**Users.** `Simple`, `EnterJoint`, `LeaveJoint`. `Config.Clone` (so `AutoLeave` off), a fresh map of
shallow `Progress` copies (sharing each ring), `checkAndReturn`, which passes at a valid
configuration: the working copy.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Api

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

/-- (internal) The working copy of the tracker (`AutoLeave` off: `Clone` drops it). -/
def Changer.checkAndCopy.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (dqc : DFrac)
    (m : Membership) (B : Base),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗
      configOwn chg.Tracker'.Config' dqc m ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m B.pv⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"go.etcd.io/raft/v3/confchange.checkAndCopy")) (Val #()))
  {{ (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err); p ↦{dqp} chg ∗ configOwn chg.Tracker'.Config' dqc m ∗ ⌜err = interface.nil⌝ ∗
      ccState B cfg trk { m with autoLeave := false } }}

end spec
end ConfChange
end EtcdGrove
end Perennial
