/- Port of election_proof/spec_MakeProgressTracker.v (feb5c73d4). -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `MakeProgressTracker` builds the **empty** tracker: fresh, empty `Votes` and
`Progress` maps, a joint configuration `[MajorityConfig{}, nil]` and nil learner sets.

This is not `ownTracker`: that predicate is for a tracker over a non-empty voter set
`cfg` (`Hcfg_ne`), and the empty tracker has none. `newRaft` never uses it as a
tracker -- it only hands it to `confchange.Restore` as the starting point, and then
`switchToConfig` overwrites its `Config` and `Progress` -- so its postcondition is the
raw pieces `Restore` reads and `ownTracker` later needs (`Votes`). -/
abbrev tracker.MakeProgressTracker.spec : Prop :=
  ∀ (maxInflight maxBytes : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker }}
    (App (App (Val #(functions tracker.MakeProgressTracker [])) (Val #maxInflight))
      (Val #maxBytes))
  {{ (tv : tracker.ProgressTracker) (v0 : Loc), RET #tv;
      ⌜tv.MaxInflight' = maxInflight ∧
        tv.MaxInflightBytes' = maxBytes ∧
        tv.Config'.Voters'.arr = [v0, map.nil] ∧
        tv.Config'.Learners' = map.nil ∧
        tv.Config'.LearnersNext' = map.nil ∧
        tv.Config'.AutoLeave' = false⌝ ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      tv.Votes' ↦$ (∅ : GMap w64 Bool) ∗
      tv.Progress' ↦$ (∅ : GMap w64 Loc) }}

end spec

end EtcdGrove
end Perennial
