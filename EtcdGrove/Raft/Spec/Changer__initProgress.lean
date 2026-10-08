/-
`Changer.initProgress` adds a fresh `Progress` for a new voter or learner. Lean-first
(no Rocq counterpart); see `InvConfchange.lean`.
-/
import EtcdGrove.Raft.InvConfchange

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

/-- `initProgress(cfg, trk, id, false)`: `id` joins the incoming voter map and gets a
fresh `Progress` (`Match = 0`, `Next = max(LastIndex, 1)`, a fresh `NewInflights`,
`StateProbe`, not a learner, recently active). Stated for `isLearner = false` only. The
`MaxInflight` bound is `NewInflights`'s premise. -/
abbrev confchange.Changer.initProgress.spec : Prop :=
  ∀ (p cfgp trk v : Loc) (chg : confchange.Changer) (cfg : tracker.Config) (id : w64)
    (vm : GMap w64 Unit) (prs : GMap w64 Loc) (dq : DFrac),
  ConfigSimple cfg v →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ cfgp ↦ cfg ∗ v ↦$ vm ∗ trk ↦$ prs }}
    (App (App (App (App
      (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"initProgress"))
      (Val #cfgp)) (Val #trk)) (Val #id)) (Val #false))
  {{ (pr : Loc) (pp : Progress), RET #();
      p ↦{dq} chg ∗ cfgp ↦ cfg ∗ v ↦$ (<[id := ()]> vm) ∗ trk ↦$ (<[id := pr]> prs) ∗
      ownProgress pr pp }}

end spec

end EtcdGrove
end Perennial
