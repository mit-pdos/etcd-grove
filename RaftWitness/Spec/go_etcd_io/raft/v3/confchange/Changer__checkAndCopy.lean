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

/-- `checkAndCopy()`: a fresh copy of the configuration (`Config.Clone`, which does not copy
`AutoLeave`) and a fresh progress map whose `Progress` objects are fresh shallow copies of
the tracker's (the same values: `ppr := *pr`), checked by `checkAndReturn`. The tracker is
only read and comes back whole. (Generalized 2026-10-12; until then the copies took the
originals' `ownProgress`, inflight rings included.) -/
abbrev confchange.Changer.checkAndCopy.spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (c : CfgM) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (dq dqc dqm dqp : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"checkAndCopy")) (Val #()))
  {{ (cfg' : tracker.Config) (trk : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg' #trk) #err);
      p ↦{dq} chg ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs ∗
      (⌜¬ CfgInv (clearAutoLeave { cfg := c, prs := flagsOf pvs }) ∧ err ≠ interface.nil⌝ ∨
       (⌜CfgInv (clearAutoLeave { cfg := c, prs := flagsOf pvs }) ∧ err = interface.nil⌝ ∗
        ownCfgCC cfg' (DFrac.own 1) { c with autoLeave := false } ∗
        ∃ (prs' : GMap w64 Loc), trk ↦$ prs' ∗ ([∗map] _k ↦ pr;pv ∈ prs';pvs, pr ↦ pv))) }}

end spec

end EtcdGrove
end Perennial
