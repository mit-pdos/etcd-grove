/- Port of election_proof/spec_ProgressTracker__Committed.v (feb5c73d4).

Lean notes: Rocq's untyped binder `tv` gets its type written out.
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC
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

/-- `p.Committed()`: the largest index a quorum of voters has acknowledged
(`tracker.ProgressTracker.Committed.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`;
tracker.go:179):

    return uint64(p.Voters.CommittedIndex(matchAckIndexer(p.Progress)))

One exit, no panic. One call, `JointConfig.CommittedIndex` on `&p.Config.Voters` with the
progress map converted to the `quorum.AckedIndexer` interface (Goose:
`interface.mkOk tracker.matchAckIndexer.ty #p.Progress`).

**At any configuration since 2026-10-13** (reconfiguration stage A1; `ownTrackerC`): the
tracker is unchanged and the result is `JCommittedIdx` of the two voter halves over the
voters' `Match` (`pvsMatchAt t.peers v`, `0` off the map, which no voter is: the map tracks
every voter): the smaller of the halves' quorum indices, an empty half counting `MaxUint64`.
The statement at a simple configuration (`ownTracker cfg`: `MaxUint64` for `cfg = ∅`,
otherwise the quorum index over `cfg`, `IsQuorumIndex`) is
`tracker.ProgressTracker.Committed.spec_simple`, which `raft.maybeCommit` uses. -/
abbrev tracker.ProgressTracker.Committed.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"Committed"))
      (Val #()))
  {{ (N : w64), RET #N;
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      ⌜JCommittedIdx c.incoming c.outgoing (pvsMatchAt t.peers) N⌝ }}

open Iris.ProofMode in
/-- The statement until 2026-10-13, at a simple configuration (`ownTracker`). -/
theorem tracker.ProgressTracker.Committed.spec_simple
    (H : tracker.ProgressTracker.Committed.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"Committed"))
      (Val #()))
  {{ (N : w64), RET #N;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      ⌜cfg = ∅ → N = W64 (2 ^ 64 - 1)⌝ ∗
      ⌜cfg ≠ ∅ → IsQuorumIndex cfg (pvsMatchAt t.peers) N⌝ }} := by
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  ihave Hown := ownTracker_toC _ _ _ $$ Hown
  iapply H _ trk tv t $$ [$Hpkg $Htrk $Hown]
  inext
  iintro %N ⟨Htrk, Hown, %HN⟩
  icases ownTrackerC_toTracker _ _ _ _ $$ Hown with ⟨Hown, -⟩
  have HN' := JCommittedIdx_simple _ _ _ HN
  iapply HΦ
  iframe Htrk Hown
  ipureintro
  exact HN'

end spec

end EtcdGrove
end Perennial
