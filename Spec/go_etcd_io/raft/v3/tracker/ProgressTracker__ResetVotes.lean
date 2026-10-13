/-
Port of `election_proof/spec_ProgressTracker__ResetVotes.v` (feb5c73d4).

Lean notes:
* The type of Rocq's untyped binder `tv` is written out (`tracker.ProgressTracker`),
  as `ownTracker` forces it. Rocq's `trk.t` record is `Trk`, and
  `t <| trk.votes := ∅ |>` is `{ t with votes := ∅ }`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

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

/-- `ResetVotes` assigns a fresh empty map to `p.Votes`, so it changes the tracker
value as well as the heap it points at. -/
abbrev tracker.ProgressTracker.ResetVotes.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ResetVotes"))
      (Val #()))
  {{ (votesRef : Loc), RET #();
      trk ↦ { tv with Votes' := votesRef } ∗
      ownTrackerC c { tv with Votes' := votesRef } { t with votes := ∅ } }}

end spec

end EtcdGrove
end Perennial
