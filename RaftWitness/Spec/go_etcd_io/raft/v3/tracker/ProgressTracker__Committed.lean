/- Port of election_proof/spec_ProgressTracker__Committed.v (feb5c73d4).

Lean notes: Rocq's untyped binder `tv` gets its type written out.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC

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
otherwise the quorum index over `cfg`, `IsQuorumIndex`) was
`tracker.ProgressTracker.Committed.spec_simple`; it had no caller and is gone (2026-10-17). -/
abbrev tracker.ProgressTracker.Committed.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"Committed"))
      (Val #()))
  {{ (N : w64), RET #N;
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      ⌜JCommittedIdx c.incoming c.outgoing (pvsMatchAt t.peers) N⌝ }}

end spec

end EtcdGrove
end Perennial
