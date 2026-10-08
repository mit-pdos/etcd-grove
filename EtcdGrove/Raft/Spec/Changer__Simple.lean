/-
`Changer.Simple` applies changes that alter the incoming config by at most one voter.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
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

/-- `Simple([AddNode id])` with `id ≠ 0` on a voters-only non-joint tracker: a fresh
copy of the config and progress map (`checkAndCopy`), with `id` added as a voter
(`apply`); the `symdiff` check passes (one voter changed at most); the result passes
`checkAndReturn`. The tracker's own maps are only read and come back, but its
`Progress` objects are not owned any more (see `checkAndCopy`). -/
abbrev confchange.Changer.Simple.spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (ccs : GoSlice) (id : w64) (v : Loc)
    (vm : GMap w64 Unit) (prs : GMap w64 Loc) (dq dqc dqv dqp : DFrac),
  id ≠ W64 0 →
  GMap.size vm < 2 ^ 63 →
  ConfigVotersOnly chg.Tracker'.Config' v →
  domSet prs = domSet vm →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ccs ↦*{dqc} [addNodeCC id] ∗
      v ↦${dqv} vm ∗ chg.Tracker'.Progress' ↦${dqp} prs ∗
      ([∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp) }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
  {{ (cfg' : tracker.Config) (trk v' : Loc) (prs' : GMap w64 Loc),
      RET (PairV (PairV #cfg' #trk) #interface.nil);
      p ↦{dq} chg ∗ ccs ↦*{dqc} [addNodeCC id] ∗
      v ↦${dqv} vm ∗ chg.Tracker'.Progress' ↦${dqp} prs ∗
      ⌜ConfigSimple cfg' v'⌝ ∗ v' ↦$ (<[id := ()]> vm) ∗ trk ↦$ prs' ∗
      ⌜domSet prs' = domSet (<[id := ()]> vm)⌝ ∗
      ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) }}

end spec

end EtcdGrove
end Perennial
