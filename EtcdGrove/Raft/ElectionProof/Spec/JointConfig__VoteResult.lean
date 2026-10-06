/-
Port of `election_proof/spec_JointConfig__VoteResult.v`.

Lean notes:
* The types of Rocq's untyped binders `tv votes` are written out
  (`tracker.ProgressTracker`, `GMap w64 Bool`), as `ownTracker` forces them.
* The reference `quorum.JointConfig__VoteResultⁱᵐᵖˡ` is to the Lean generated code
  `quorum.JointConfig.VoteResult.impl`.
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

/-- `c.VoteResult(votes)` for the joint config, i.e. the last statement of
`TallyVotes`. The receiver is `&r.trk.Config.Voters`, the same field ref `campaign`
passes to `JointConfig.IDs`.

The body (`quorum.JointConfig.VoteResult.impl`, joint.go:62) asks each component and
combines:

    r1 := c[0].VoteResult(votes)
    r2 := c[1].VoteResult(votes)
    if r1 == r2 { return r1 }
    if r1 == VoteLost || r2 == VoteLost { return VoteLost }
    return VotePending

The configuration here is *simple*, so `ownTracker`'s `Hvoters_arr` says the array is
`[voters_ref, map.nil]`: the second component is empty and
`MajorityConfig.VoteResult` answers `VoteWon` for it by convention. The combination
then returns `r1` whatever it is -- `VoteWon` through the first test, `VoteLost`
through the second, `VotePending` through the fall-through -- so the joint answer is
exactly the answer for `cfg`.

Both conjuncts are equivalences, not implications: nothing here is lost. The premise
`cfg ≠ ∅` is what makes that true. `MajorityConfig.VoteResult` returns `VoteWon`
outright for an empty config ("by convention, the elections on an empty config win"),
while `IsQuorum ∅ q` unfolds to `0 < 2 * 0` and is false, so at `cfg = ∅` the `VoteWon`
conjunct would fail. The premise used to be a conjunct of `ownTracker`; it was moved
here so that the empty tracker is an `ownTracker ∅ …`. In the proof it refutes the
`map.nil` disjunct of `MajorityConfig.wp_VoteResult`'s postcondition for the first
component. -/
abbrev quorum.JointConfig.VoteResult.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)),
  cfg ≠ ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ trk ↦ tv ∗
      ownTracker cfg tv votes prs pvs }}
    (App (Val ((trk.[tracker.ProgressTracker, go!"Config"]).[tracker.Config, go!"Voters"]
        @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"VoteResult"))
      (Val #(tv.Votes')))
  {{ (res : w8), RET #res;
      trk ↦ tv ∗ ownTracker cfg tv votes prs pvs ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ IsQuorum cfg (granted votes)⌝ ∗
      -- `VoteLost` is "cannot still win", not "a majority rejected"; see
      -- `spec_ProgressTracker__TallyVotes.v` and `Protocol.lean`'s `Step.lose`.
      ⌜res = VoteLost ↔ ¬ IsQuorum cfg (cfg \ rejected votes)⌝ }}

end spec

end EtcdGrove
end Perennial
