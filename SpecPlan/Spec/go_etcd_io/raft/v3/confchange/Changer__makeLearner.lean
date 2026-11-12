/-
## `Changer.makeLearner(cfg, trk, id)` (internal)

**Users.** `apply` (and `makeLearner` calls `remove`). Mirrors the code: the model's `makeLearner` on
the working copy (map writes through `nilAwareAdd`/`nilAwareDelete`; a new peer by
`initProgress`).
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

/-- (internal) Makes `id` a learner (staged if an outgoing voter). -/
def Changer.makeLearner.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (B : Base)
    (cfgp : Loc) (trk : GoMap) (m : Membership) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗ ccWork B cfgp trk m ∗ ⌜BaseOf chg B⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"go.etcd.io/raft/v3/confchange.makeLearner")) (Val #cfgp)) (Val #trk)) (Val #id))
  {{ RET #(); p ↦{dqp} chg ∗ ccWork B cfgp trk (makeLearner id m) }}

end spec
end ConfChange
end EtcdGrove
end Perennial
