/-
Port of `election_proof/spec_ProgressTracker__ResetVotes.v`.

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

/-- `ResetVotes` assigns a fresh empty map to `p.Votes`, so it changes the tracker
value as well as the heap it points at. -/
abbrev tracker.ProgressTracker.ResetVotes.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv votes prs pvs }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ResetVotes"))
      (Val #()))
  {{ (votesRef : Loc), RET #();
      trk ↦ { tv with Votes' := votesRef } ∗
      ownTracker cfg { tv with Votes' := votesRef } ∅ prs pvs }}

end spec

end EtcdGrove
end Perennial
