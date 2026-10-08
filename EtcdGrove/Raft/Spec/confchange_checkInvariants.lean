/-
`confchange.checkInvariants(cfg, trk)` checks that a config and a progress map agree.
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

/-- On a voters-only non-joint config whose progress map has exactly the voters' ids,
`checkInvariants` returns `nil`: every voter has a progress; the learner loops range over
`nil` maps; the non-joint checks (`Voters[1]`, `LearnersNext` nil, `AutoLeave` off) hold
by `ConfigSimple`. The `Progress` values are never read (only the learner loops read
`IsLearner`, and they run zero times), so only the maps are needed. -/
abbrev confchange.checkInvariants.spec : Prop :=
  ∀ (cfg : tracker.Config) (trk v : Loc) (vm : GMap w64 Unit) (prs : GMap w64 Loc)
    (dqv dqp : DFrac),
  ConfigSimple cfg v →
  domSet prs = domSet vm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ v ↦${dqv} vm ∗ trk ↦${dqp} prs }}
    (App (App (Val #(functions confchange.checkInvariants [])) (Val #cfg)) (Val #trk))
  {{ RET #interface.nil; v ↦${dqv} vm ∗ trk ↦${dqp} prs }}

end spec

end EtcdGrove
end Perennial
