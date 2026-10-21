/-
`Changer.makeLearner` makes an id a learner, or stages it in `LearnersNext`.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `makeLearner(cfg, trk, id)`: `makeLearnerM`. raft#168 made it return an `error` ("cannot
change witness to non-witness learner") and clear `IsWitness` when it makes a voter a learner:
on a witness-free configuration it is `nil`, and the rest is as before. -/
abbrev confchange.Changer.makeLearner.spec : Prop :=
  ∀ (p cfgp trk : Loc) (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (s : CCState) (id : w64) (dq : DFrac),
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ownWork chg base cfgp trk s }}
    (App (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"makeLearner")) (Val #cfgp)) (Val #trk)) (Val #id))
  {{ (err : GoInterface), RET #err; p ↦{dq} chg ∗
      ownWorkO chg base cfgp trk (makeLearnerO id s) err }}

end spec

end EtcdGrove
end Perennial
