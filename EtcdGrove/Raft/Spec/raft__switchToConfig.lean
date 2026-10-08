/-
Port of election_proof/spec_raft__switchToConfig.v (feb5c73d4).

Lean notes:
* Rocq's `s <| nstate.progress := prs |> <| nstate.prvals := pvs |>` is
  `{ s with progress := prs, prvals := pvs }` (the same value), and the type of the
  untyped binder `pvs` is written out.
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.switchToConfig(cfg, trk)` installs a configuration and progress map in `r.trk`,
sets `r.isLearner`, and returns the tracker's `ConfState`.

**Only the non-leader case is specified** (`s.role ≠ .leader`). There the function
returns right after computing `cs`: both of its leader branches -- stepping down on
removal, and `maybeCommit`/`bcastAppend` to the new configuration -- are guarded by
`state == StateLeader`. That is the case `newRaft` needs, the only caller in scope
(reconfiguration, `applyConfChange`, is out of scope).

**It changes the configuration** `ownRaftPhys` is indexed by, from `cfg0` to `cfg`, and
the progress map with it: the new `Config` and progress map come in as `ownConfig`
(what `confchange.Restore` builds), and the struct goes out at `cfg`
(`ownRaftPhys_reconfig`, `ownTracker_reconfig`). Until 2026-09-29 the tracker was held
on loan across the call instead, because the empty tracker `newRaft` starts from was
not an `ownTracker`.

`r.isLearner` ends up `false`: it is `ok && pr.IsLearner`, and every `Progress` in
`ownTracker` has `IsLearner = false`. -/
abbrev raft.switchToConfig.spec : Prop :=
  ∀ (cfg0 cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc),
  s.role ≠ .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg0 r id s ∗
      ownConfig cfg cfgv prsm prs }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
      (Val #cfgv)) (Val #prsm))
  {{ (cs : raftpb.ConfState) (xs : List w64)
      (pvs : GMap w64 Progress), RET #cs;
      ownRaftPhys cfg r id { s with progress := prs, prvals := pvs } ∗
      cs.Voters' ↦* xs ∗ ⌜xs ≡ₚ elements cfg⌝ ∗
      ⌜cs.VotersOutgoing'.len = W64 0 ∧
        cs.Learners'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ }}

end spec

end EtcdGrove
end Perennial
