/-
Port of `election_proof/spec_ProgressTracker__RecordVote.v`.

Lean notes: the Rocq binder `from` is `src` (`from` is a Lean keyword). Rocq leaves
the types of `tv` and `votes` implicit; they are written out (`tracker.ProgressTracker`,
`GMap w64 Bool`, as in `ownTracker`).
-/
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

/-- `RecordVote` only inserts into the map `p.Votes` already refers to, so the tracker
value is unchanged. First write wins, which is `recordVote`. -/
abbrev tracker.ProgressTracker.RecordVote.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (src : w64) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv votes prs pvs }}
    (App (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"RecordVote"))
      (Val #src)) (Val #v))
  {{ RET #(); trk ↦ tv ∗ ownTracker cfg tv (recordVote votes src v) prs pvs }}

end spec

end EtcdGrove
end Perennial
