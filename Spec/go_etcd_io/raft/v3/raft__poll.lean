/-
Port of election_proof/spec_raft__poll.v (feb5c73d4).

Lean notes:
the Rocq binder `from` is `src` (`from` is a Lean keyword), as in
`recordVote`. The postcondition's `let votes' := …` is kept; its body is wrapped in
`iprop(…)` so that the separating conjunction elaborates after the `let`. The return
`(#g, #rj, #res)` is `PairV (PairV #g #rj) #res`.
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

/-- `poll` records a vote and reports the tally, tied to the model's quorum conditions
by `tracker.ProgressTracker.TallyVotes.spec`.

At any configuration since 2026-10-13 (reconfiguration stage A2): the answer is exactly
`JQuorum`/`JLost` of the joint configuration (`Protocol/StepC.lean`), with no premise -- Go's
empty half wins every vote, which `MajQ` says. The statement at a simple configuration
(`cfg ≠ ∅`, `IsQuorum cfg`) is `raft.poll.specS`. -/
abbrev raft.poll.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (src : w64) (t : w32) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"poll"))
      (Val #src)) (Val #t)) (Val #v))
  {{ (g rj : w64) (res : w8), RET (PairV (PairV #g #rj) #res);
      let votes' := recordVote s.votes src v
      iprop(ownRaftPhysCV c c.voters r id { s with votes := votes' } ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ JQuorum c (granted votes')⌝ ∗
      -- see InvTracker.lean: `VoteLost` is "cannot still win", not "a majority
      -- rejected"
      ⌜res = VoteLost ↔ JLost c votes'⌝) }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.poll.spec` by `raft.poll.spec_simple`. -/
abbrev raft.poll.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (src : w64) (t : w32) (v : Bool),
  cfg ≠ ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"poll"))
      (Val #src)) (Val #t)) (Val #v))
  {{ (g rj : w64) (res : w8), RET (PairV (PairV #g #rj) #res);
      let votes' := recordVote s.votes src v
      iprop(ownRaftPhys cfg r id { s with votes := votes' } ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon → IsQuorum cfg (granted votes')⌝ ∗
      ⌜res = VoteLost → ¬ IsQuorum cfg (cfg \ rejected votes')⌝) }}

open Iris.ProofMode in
theorem raft.poll.spec_simple
    (H : raft.poll.spec (GF := GF) (hG := hG)) :
    raft.poll.specS (GF := GF) (hG := hG) := by
  intro cfg r id s src t v Hne
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s src t v $$ [$Hpkg $Hphys]
  inext
  iintro %g %rj %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  dsimp only
  iframe Hphys
  ipureintro
  exact ⟨Hres, fun h => (JQuorum_of_out (c := CfgM.simple cfg (domSet s.progress \ cfg)) Hne rfl _).1
      (Hwon.1 h),
    fun h => (JLost_of_out (c := CfgM.simple cfg (domSet s.progress \ cfg)) Hne rfl _).1 (Hlost.1 h)⟩

end spec

end EtcdGrove
end Perennial
