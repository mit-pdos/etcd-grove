/-
`confchange.checkInvariants(cfg, trk)` checks that a config and a progress map agree.
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

/-- `checkInvariants(cfg, trk)` returns `nil` exactly when the configuration and the
progress map satisfy `CfgInv` (each id's `IsLearner` read from its `Progress`), an error
otherwise. Everything is only read. (Generalized 2026-10-12 from the voters-only case.) -/
abbrev confchange.checkInvariants.spec : Prop :=
  ∀ (cfg : tracker.Config) (trk : Loc) (c : CfgM) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (dqc dqm dqp : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) }}
    (App (App (Val #(functions confchange.checkInvariants [])) (Val #cfg)) (Val #trk))
  {{ (err : GoInterface), RET #err; ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
      ⌜err = interface.nil ↔ CfgInv { cfg := c, prs := flagsOf pvs }⌝ }}

end spec

end EtcdGrove
end Perennial
