/-
`confchange.checkAndReturn(cfg, trk)` is `checkInvariants` returning its arguments.
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

/-- `checkAndReturn(cfg, trk)`: `(cfg, trk, nil)` if `checkInvariants` accepts them, an
error otherwise. (Generalized 2026-10-12 from the voters-only case.) -/
abbrev confchange.checkAndReturn.spec : Prop :=
  ∀ (cfg : tracker.Config) (trk : Loc) (c : CfgM) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (dqc dqm dqp : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) }}
    (App (App (Val #(functions confchange.checkAndReturn [])) (Val #cfg)) (Val #trk))
  {{ (cfg' : tracker.Config) (trk' : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg' #trk') #err); ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
      ⌜(CfgInv { cfg := c, prs := flagsOf pvs } ∧ err = interface.nil ∧ cfg' = cfg ∧ trk' = trk) ∨
        (¬ CfgInv { cfg := c, prs := flagsOf pvs } ∧ err ≠ interface.nil)⌝ }}

end spec

end EtcdGrove
end Perennial
