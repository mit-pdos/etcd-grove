/-
## `Changer.initProgress(cfg, trk, id, isLearner)` (internal)

**Users.** `makeVoter`, `makeLearner`, for an untracked id. Mirrors the code: an incoming voter or a
learner, with a fresh `Progress` (`NewInflights` at the tracker's capacities: the bound is
`BaseOf`'s).
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

/-- (internal) Tracks the new peer `id`, a voter or a learner. -/
def Changer.initProgress.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (B : Base)
    (cfgp : Loc) (trk : GoMap) (m : Membership) (id : w64) (isLearner : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗ ccWork B cfgp trk m ∗ ⌜BaseOf chg B⌝ ∗ ⌜id ∉ m.ids⌝ }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"go.etcd.io/raft/v3/confchange.initProgress")) (Val #cfgp)) (Val #trk)) (Val #id)) (Val #isLearner))
  {{ RET #(); p ↦{dqp} chg ∗
      ccWork B cfgp trk (if isLearner then { m with learners := m.learners ∪ {[id]} }
        else { m with voters := m.voters ∪ {[id]} }) }}

end spec
end ConfChange
end EtcdGrove
end Perennial
