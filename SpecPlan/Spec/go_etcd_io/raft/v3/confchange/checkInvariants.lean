/-
## `checkInvariants(cfg, trk)` (internal)

**Users.** `checkAndReturn`. Mirrors the code on the working copy (whose progress map tracks
exactly its ids, learners marked, and whose non-joint maps are `nil` when empty): an error exactly
when `CfgOk` fails.
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

/-- (internal) No error iff the configuration passes `checkInvariants`' checks (`CfgOk`). -/
def checkInvariants.spec : Prop :=
  ∀ (B : Base) (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (m : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ccState B cfg trk m }}
    (App (App (Val #(functions go_etcd_io.raft.v3.confchange.checkInvariants [])) (Val #cfg)) (Val #trk))
  {{ (err : GoInterface), RET #err; ccState B cfg trk m ∗
      ⌜err = interface.nil ↔ m.CfgOk⌝ }}

end spec
end ConfChange
end EtcdGrove
end Perennial
