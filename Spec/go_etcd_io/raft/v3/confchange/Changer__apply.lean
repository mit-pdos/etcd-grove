/-
`Changer.apply` applies a list of single changes to a config. Lean-first (no Rocq
counterpart); see `InvConfchange.lean`.
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

/-- `apply(cfg, trk, [AddNode id])` with `id ≠ 0` on a voters-only non-joint config:
`makeVoter`, then the "removed all voters" check passes (the map has `id`). Stated for
the one change list this path applies. `NodeID = 0` is what `apply` skips, so it is
excluded rather than specified. The size bound is what makes the `len` comparison
meaningful (a 64-bit `int`); `Restore` has it from the voters being a Go slice. -/
abbrev confchange.Changer.apply.spec : Prop :=
  ∀ (p cfgp trk v : Loc) (chg : confchange.Changer) (cfg : tracker.Config)
    (ccs : GoSlice) (id : w64) (vm : GMap w64 Unit) (prs : GMap w64 Loc) (dq dqc : DFrac),
  id ≠ W64 0 →
  GMap.size vm < 2 ^ 63 →
  ConfigSimple cfg v →
  domSet prs = domSet vm →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ cfgp ↦ cfg ∗ ccs ↦*{dqc} [addNodeCC id] ∗
      v ↦$ vm ∗ trk ↦$ prs ∗ ([∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp) }}
    (App (App (App
      (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"apply"))
      (Val #cfgp)) (Val #trk)) (Val #ccs))
  {{ (prs' : GMap w64 Loc), RET #interface.nil;
      p ↦{dq} chg ∗ cfgp ↦ cfg ∗ ccs ↦*{dqc} [addNodeCC id] ∗
      v ↦$ (<[id := ()]> vm) ∗ trk ↦$ prs' ∗ ⌜domSet prs' = domSet (<[id := ()]> vm)⌝ ∗
      ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) }}

end spec

end EtcdGrove
end Perennial
