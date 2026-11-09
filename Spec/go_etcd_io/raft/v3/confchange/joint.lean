/-
## `joint(cfg)` (internal)

**Users.** `Simple`, `EnterJoint`, `LeaveJoint`, `checkInvariants`. Mirrors the code: the outgoing
half's `len`.
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

/-- (internal) Whether the configuration is joint (an outgoing voter). -/
def joint.spec : Prop :=
  ∀ (cfg : go_etcd_io.raft.v3.tracker.Config) (dq : DFrac) (s0 s1 : GSet w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ Quorum.jointConfigOwn cfg.Voters' dq s0 s1 }}
    (App (Val #(functions go_etcd_io.raft.v3.confchange.joint [])) (Val #cfg))
  {{ RET #(decide (s1 ≠ ∅)); Quorum.jointConfigOwn cfg.Voters' dq s0 s1 }}

end spec
end ConfChange
end EtcdGrove
end Perennial
