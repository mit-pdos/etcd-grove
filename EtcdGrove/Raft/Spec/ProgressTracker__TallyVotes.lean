/-
Port of election_proof/spec_ProgressTracker__TallyVotes.v (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `TallyVotes` reports the outcome of the election, which is exactly the quorum
condition of the model.

**Proved 2026-09-20** (`proof_ProgressTracker__TallyVotes.v`). The function counts the
granted and rejected `t.votes` over `trk.Progress` and then delegates the verdict to
`p.Config.Voters.VoteResult(p.Votes)` (`spec_JointConfig__VoteResult.v` and, under it,
`spec_MajorityConfig__VoteResult.v`), which is where the quorum arithmetic lives. What
the loop here contributes is the two counters, and they are *not* what the
postcondition talks about: the returned `g`/`rj` are existentially quantified, since no
caller reads them (`poll` returns them to `stepCandidate`, which only looks at `res`).

Three things had to be fixed before this could be proved, all recorded here because
each cost a day:

- **Array indexing.** `quorum.JointConfig` is `[2]MajorityConfig`, and Goose
  translated `c[0]` as `IndexRef` applied to the array *value*, where
  `index_ref_array` only steps on an array *location*. Fixed in Goose 2026-09-17; see
  `spec_JointConfig__IDs.v` for the write-up.

- **`len` of a nil map.** The second component of a simple configuration is
  `map.nil`, and `MajorityConfig.VoteResult` begins with `len(c) == 0`.
  `pure_wp_map_nil_len` (`new/golang/theory/map.v`) handles it; the
  `go.len_underlying` detour a map of a *named* type needs is in
  `proof_MajorityConfig__VoteResult_helpers/majority_len.v`.

The `VoteWon` conjunct is false at `cfg = ∅` -- `MajorityConfig.VoteResult` returns
`VoteWon` outright for an empty config ("by convention, the elections on an empty
config win"), while `IsQuorum ∅ q` unfolds to `0 < 2 * 0`. That is why this spec (like
`JointConfig.wp_VoteResult`, which it passes the premise to) takes `cfg ≠ ∅`; the fact
used to be a conjunct of `ownTracker`, and was moved out so that the empty tracker is
an `ownTracker ∅ …`. -/
abbrev tracker.ProgressTracker.TallyVotes.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  cfg ≠ ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"TallyVotes"))
      (Val #()))
  {{ (g rj : w64) (res : w8), RET (PairV (PairV #g #rj) #res);
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon → IsQuorum cfg (granted t.votes)⌝ ∗
      -- `VoteLost` means the candidate **cannot still win**, not that a majority
      -- rejected -- Go computes `votedCnt + missing < q`, and
      -- `votedCnt + missing = size (cfg \ rejected)`. The old form,
      -- `IsQuorum cfg (rejected t.votes)`, was false: 4 voters with 2 rejecting and 2
      -- silent gives `VoteLost` with no rejection quorum. Corrected 2026-09-16; see
      -- `Protocol.lean`'s `Step.lose`.
      ⌜res = VoteLost → ¬ IsQuorum cfg (cfg \ rejected t.votes)⌝ }}

end spec

end EtcdGrove
end Perennial
