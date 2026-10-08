/-
Port of election_proof/spec_raft__poll.v (feb5c73d4).

Lean notes:
the Rocq binder `from` is `src` (`from` is a Lean keyword), as in
`recordVote`. The postcondition's `let votes' := …` is kept; its body is wrapped in
`iprop(…)` so that the separating conjunction elaborates after the `let`. The return
`(#g, #rj, #res)` is `PairV (PairV #g #rj) #res`.
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

/-- `poll` records a vote and reports the tally, tied to the model's quorum conditions
by `tracker.ProgressTracker.TallyVotes.spec`. -/
abbrev raft.poll.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (src : w64) (t : w32) (v : Bool),
  -- `TallyVotes` needs it: an empty config "wins" every election in Go but is never a
  -- quorum in the model; see `Spec/JointConfig__VoteResult.lean`
  cfg ≠ ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"poll"))
      (Val #src)) (Val #t)) (Val #v))
  {{ (g rj : w64) (res : w8), RET (PairV (PairV #g #rj) #res);
      let votes' := recordVote s.votes src v
      iprop(ownRaftPhys cfg r id { s with votes := votes' } ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon → IsQuorum cfg (granted votes')⌝ ∗
      -- see InvTracker.lean: `VoteLost` is "cannot still win", not "a majority
      -- rejected"
      ⌜res = VoteLost → ¬ IsQuorum cfg (cfg \ rejected votes')⌝) }}

end spec

end EtcdGrove
end Perennial
