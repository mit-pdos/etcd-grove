/-
## `Changer.apply(cfg, trk, ccs...)` (internal)

**Users.** `Simple`, `EnterJoint`. The loop over the changes (`applyOne`: `makeVoter`,
`makeLearner`, `remove`, skip, or the "unexpected conf type" error), then the "removed all voters"
check. Mirrors the code (the model's `apply`); an error leaves some working copy.
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

/-- (internal) The changes on the working copy: the model's `apply`. -/
def Changer.apply.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (B : Base)
    (cfgp : Loc) (trk : GoMap) (m : Membership) (sl : GoSlice) (dqs : DFrac) (cs : List Single),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗ ccWork B cfgp trk m ∗ ⌜BaseOf chg B⌝ ∗ ccsPts sl dqs cs }}
    (App (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"go.etcd.io/raft/v3/confchange.apply")) (Val #cfgp)) (Val #trk)) (Val #sl))
  {{ (err : GoInterface), RET #err; p ↦{dqp} chg ∗ ccsPts sl dqs cs ∗
      match apply cs m with
      | some m1 => ⌜err = interface.nil⌝ ∗ ccWork B cfgp trk m1
      | none => ⌜err ≠ interface.nil⌝ ∗ ∃ m1, ccWork B cfgp trk m1 }}

end spec
end ConfChange
end EtcdGrove
end Perennial
