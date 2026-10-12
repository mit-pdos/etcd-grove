/-
`Changer.checkAndCopy` clones the tracker's config and progress map and checks them.
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

/-- `checkAndCopy` on a voters-only non-joint tracker: a fresh config (`Config.Clone`)
with the same voters, and a fresh progress map holding a shallow copy of each
`Progress`. **A shallow copy shares the `Inflights` pointer** (`ppr := *pr`), so the
copies' `ownProgress` take the inflight rings from the originals: what comes back for
the original map is its points-to only, its `Progress` objects are not owned any more.
On this path the originals are garbage after the call (`chain` replaces them), except
`MakeProgressTracker`'s empty map, which has no `Progress` to lose. -/
abbrev confchange.Changer.checkAndCopy.spec : Prop :=
  ∀ (chg : confchange.Changer) (v : Loc) (vm : GMap w64 Unit)
    (prs : GMap w64 Loc) (dqv dqp : DFrac),
  ConfigVotersOnly chg.Tracker'.Config' v →
  domSet prs = domSet vm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ v ↦${dqv} vm ∗ chg.Tracker'.Progress' ↦${dqp} prs ∗
      ([∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp) }}
    (App (Val (chg @!! confchange.Changer.ty @!! go!"checkAndCopy"))
      (Val #()))
  {{ (cfg' : tracker.Config) (trk v' : Loc) (prs' : GMap w64 Loc),
      RET (PairV (PairV #cfg' #trk) #interface.nil);
      v ↦${dqv} vm ∗ chg.Tracker'.Progress' ↦${dqp} prs ∗
      ⌜ConfigSimple cfg' v'⌝ ∗ v' ↦$ vm ∗ trk ↦$ prs' ∗ ⌜domSet prs' = domSet vm⌝ ∗
      ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) }}

end spec

end EtcdGrove
end Perennial
