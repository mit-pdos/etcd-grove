/-
`Changer.makeVoter` adds or promotes an id to a voter of the incoming config.
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

/-- `makeVoter(cfg, trk, id)` on a voters-only non-joint config: afterwards `id` is a
voter with an owned `Progress`. A new id goes through `initProgress`; an id already
present (a repeated voter in the `ConfState`) keeps its `Progress`, re-marked a
non-learner, and the `nilAwareDelete`s on the `nil` learner maps are no-ops. -/
abbrev confchange.Changer.makeVoter.spec : Prop :=
  ∀ (cfgp trk v : Loc) (chg : confchange.Changer) (cfg : tracker.Config) (id : w64)
    (vm : GMap w64 Unit) (prs : GMap w64 Loc),
  ConfigSimple cfg v →
  domSet prs = domSet vm →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ cfgp ↦ cfg ∗ v ↦$ vm ∗ trk ↦$ prs ∗
      ([∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp) }}
    (App (App (App
      (Val (chg @!! confchange.Changer.ty @!! go!"makeVoter"))
      (Val #cfgp)) (Val #trk)) (Val #id))
  {{ (prs' : GMap w64 Loc), RET #();
      cfgp ↦ cfg ∗ v ↦$ (<[id := ()]> vm) ∗ trk ↦$ prs' ∗
      ⌜domSet prs' = domSet (<[id := ()]> vm)⌝ ∗
      ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) }}

end spec

end EtcdGrove
end Perennial
