/-
`Changer.remove` removes an id as a voter or learner from the incoming config.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

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

/-- `remove(cfg, trk, id)`: `removeM` on the configuration; the progress map loses `id` when
it is tracked but no outgoing voter. Only the map is touched, not the `Progress` objects,
so the caller keeps them (`makeLearner` puts the one it removed back). -/
abbrev confchange.Changer.remove.spec : Prop :=
  ∀ (p cfgp trk : Loc) (chg : confchange.Changer) (s : CCState) (prs : GMap w64 Loc)
    (id : w64) (dq : DFrac),
  domSet prs = domSet s.prs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ownCfgAt cfgp s.cfg ∗ trk ↦$ prs }}
    (App (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"remove")) (Val #cfgp)) (Val #trk)) (Val #id))
  {{ RET #(); p ↦{dq} chg ∗ ownCfgAt cfgp (removeM id s).cfg ∗
      trk ↦$ (if id ∈ s.prs ∧ id ∉ s.cfg.outgoing then GMap.delete id prs else prs) }}

end spec

end EtcdGrove
end Perennial
