/- Port of election_proof/spec_ProgressTracker__Committed.v (feb5c73d4).

Lean notes: Rocq's untyped binder `tv` gets its type written out.
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

/-- `p.Committed()`: the largest index a quorum of voters has acknowledged
(`tracker.ProgressTracker.Committed.impl`,
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`; tracker.go:179):

    return uint64(p.Voters.CommittedIndex(matchAckIndexer(p.Progress)))

One exit, no panic. One call, `JointConfig.CommittedIndex` on `&p.Config.Voters` with
the progress map converted to the `quorum.AckedIndexer` interface (Goose:
`Convert matchAckIndexer quorum.AckedIndexer (![ProgressMap] p.Progress)`, i.e.
`interface.mkOk tracker.matchAckIndexer.ty #p.Progress`).

The tracker is unchanged. The result `N` is `MaxUint64` for an empty configuration
(never the case for a raft node, whose voter set contains itself, but `ownTracker`
allows it), and otherwise the quorum index of the voters' `Match` (`IsQuorumIndex`,
`InvTracker.lean`):

  - `N` is some voter's `Match`;
  - `IsQuorum cfg (filter (fun v => N ≤ Match v) cfg)` -- a quorum of voters have
    acknowledged `N`, in `Protocol/Model.lean`'s sense of `IsQuorum`
    (`size cfg < 2 * size (q ∩ cfg)`);
  - no larger index has such a quorum.

`pvsMatchAt t.peers v` is `v`'s `Match` (`0` off the map, which no voter is:
`ownTracker`'s maps have domain `cfg`). -/
abbrev tracker.ProgressTracker.Committed.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"Committed"))
      (Val #()))
  {{ (N : w64), RET #N;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      ⌜cfg = ∅ → N = W64 (2 ^ 64 - 1)⌝ ∗
      ⌜cfg ≠ ∅ → IsQuorumIndex cfg (pvsMatchAt t.peers) N⌝ }}

end spec

end EtcdGrove
end Perennial
