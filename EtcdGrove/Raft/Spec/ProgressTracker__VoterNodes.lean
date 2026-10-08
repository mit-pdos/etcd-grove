/-
Port of `election_proof/spec_ProgressTracker__VoterNodes.v` (feb5c73d4).

Lean notes: Rocq leaves the type of `tv` implicit; it is written out
(`tracker.ProgressTracker`, as in `ownTracker`). Rocq's `trk.t` record is `Trk`. `elements cfg` is
`GMap.elements cfg`.
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

/-- `p.VoterNodes()` is the voter ids, sorted. As for `MajorityConfig.Slice`, only the
permutation is stated. `newRaft` uses it only to build a log line. -/
abbrev tracker.ProgressTracker.VoterNodes.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"VoterNodes"))
      (Val #()))
  {{ (sl : GoSlice) (xs : List w64), RET #sl;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      sl ↦* xs ∗ ⌜xs ≡ₚ GMap.elements cfg⌝ }}

end spec

end EtcdGrove
end Perennial
