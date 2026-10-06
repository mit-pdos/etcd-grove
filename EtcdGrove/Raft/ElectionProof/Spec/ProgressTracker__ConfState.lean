/-
Port of `election_proof/spec_ProgressTracker__ConfState.v`.

Lean notes:
* The types of Rocq's untyped binders `tv votes` are written out
  (`tracker.ProgressTracker`, `GMap w64 Bool`), as `ownTracker` forces them.
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

/-- `p.ConfState()` is the `ConfState` of the active configuration: the voters (some
permutation of `cfg`; really sorted), and -- since `ownTracker` is a simple
configuration with no learners -- empty `VotersOutgoing`, `Learners` and
`LearnersNext`. Only `Voters` is handed back with its elements; for the others their
length is all any caller needs. -/
abbrev tracker.ProgressTracker.ConfState.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv votes prs pvs }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ConfState"))
      (Val #()))
  {{ (cs : raftpb.ConfState) (xs : List w64), RET #cs;
      trk ↦ tv ∗ ownTracker cfg tv votes prs pvs ∗
      cs.Voters' ↦* xs ∗ ⌜xs ≡ₚ elements cfg⌝ ∗
      ⌜cs.VotersOutgoing'.len = W64 0 ∧
        cs.Learners'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ }}

end spec

end EtcdGrove
end Perennial
