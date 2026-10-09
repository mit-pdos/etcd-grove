/-
Port of `election_proof/election.v` (at 857d09190), the lemmas after its `Require`s; the
`Require`s themselves are `Link.lean` (generated) and `MemstorageInstance.lean`.

### Refinement of etcd raft

`Link.lean` is the aggregator. Every Hoare triple lives in its own spec/proof pair
under `Raft/` (`Spec/<fn>.lean`, `Proof/<fn>.lean`; Rocq's
spec/postulates/proof/link quadruple), and `Link.lean` instantiates every proof with
its callees' results; importing `Link.lean` from the root module (`EtcdGrove.lean`)
is what keeps the build honest, since `lake build` builds only what the root reaches, and
a link nothing imported would silently go unchecked.

The top-level result is `raft.wp_Step` (`Link.lean`): running `Step` on a
message takes the physical raft struct from a state refining the protocol state `s` to
one refining `s'`, and the ghost protocol state can be moved from `s` to `s'` at the same
time -- i.e. the implementation refines the protocol of `Protocol/`. Beside
it: `RawNode.wp_Propose`, the client's entry point (one `Step` of a `MsgProp`), and
`wp_newRaft`, the constructor, which establishes `ownRaftPhys` (`Spec/newRaft.lean`).
The `RawNode` results (`wp_Propose`, `wp_Ready`, `wp_Advance`, `wp_HasReady`) are
client-facing since 2026-10-09: stated on `ownRawNode γ rn id rs` (`InvRawnode.lean`),
with no protocol state in them; the refinement above is how they are proved.

Scope, matching `Protocol/`:
  - no pre-vote, no check-quorum,
  - no proposals, no read-only requests,
  - no reconfiguration and no learners.

Trust boundary. Two kinds, and the layout keeps them apart:
  - A `Proof/<fn>.lean` of a function outside the scope is an `axiom <fn>.wp_proof`.
    These are Lean `axiom`s. The client-supplied interfaces are not: `isLogger` is a
    definition (the triples a client supplies), and `ownStorage` is a parameter, the
    field of `StorageModel GF`, so the results hold for every storage predicate
    (both axioms until 2026-10-08).
  - A function that is in scope but unfinished is a `sorry` inside its own
    `Proof/<fn>.lean`.
Nothing in a proof theorem's hypothesis list is an assumption: a callee spec taken as a
hypothesis (Rocq's `postulates_*.v`, a `Module Type`) is discharged in `Link.lean` by
the callee's own result, and adds nothing to `#print axioms`. The `#print axioms` at the
end of this file print the trust base of the top-level results in the build log.

Lean notes:
* `raft_election_safety`'s comment says, as the Rocq does, that it "cannot yet serve
  even that purpose" because the ghost state has no allocation lemma. That is out of date
  in Rocq too: `own_raft_ghost_alloc` exists (here `ownRaftGhost_alloc`,
  `Protocol/Facts.lean`), allocating a fresh ghost state for any set of nodes at
  `initPState`, so the ghost predicates are inhabited; and in Lean the ghost state is
  defined (`Protocol/GhostState.lean`), not axiomatized. The comment below is adapted.
* `newRaft_post_init` takes its premise in the shape of `newRaft`'s postcondition
  (`Spec/newRaft.lean`) minus the `s.prevote = cv.PreVote'` conjunct, as the Rocq does.
-/
module

public import Proof.go_etcd_io.raft.v3.Link

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF] [StorageModel GF]

/-- **Sanity check on the model: election safety.**

Two nodes that `Step` leaves in the leader role in the same term are the same node.

This is **not** the result of the development -- `raft.wp_Step` (`Link.lean`) is,
along with the other top-level function specs. A verified spec for a Go function is what
a client of this proof consumes; a protocol-level theorem is an internal detail in
service of one. What this corollary is for is evidence that `PState` and `step` entail
the property raft exists to provide, and so were not defined into triviality; that it is
not vacuous rests on `ownRaftGhost_alloc` (`Protocol/Facts.lean`), which shows the ghost
state inhabited (see the Lean notes above). See the Rocq repository's
notes/decisions.md, 2026-09-21. -/
theorem raft_election_safety (γ : RaftNames) (id1 id2 : w64) (s1 s2 : PState) :
    s1.role = .leader →
    s2.role = .leader →
    s1.term = s2.term →
    ⊢ ownRaftGhost (GF := GF) γ id1 s1 -∗ ownRaftGhost γ id2 s2 -∗ ⌜id1 = id2⌝ := by
  intro Hl1 Hl2 Hterm
  iintro H1 H2
  ihave #Hle1 := ownRaftGhost_isLeader γ id1 s1 Hl1 $$ H1
  ihave #Hle2 := ownRaftGhost_isLeader γ id2 s2 Hl2 $$ H2
  rw [Hterm]
  iapply isLeader_unique γ id1 id2 s2.term $$ Hle1 Hle2

end proof

section newRaft_post
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- `newRaft`'s postcondition, on a storage with no persisted `HardState` and an empty
log, is the protocol's initial state. (Since 2026-10-01 the protocol state has the log,
and `initPState`'s is empty: a node starting from a storage that already holds entries
is not at `initPState`, and `ownRaftGhost_alloc` does not cover it -- its entries would
need `isEntry`s.) -/
theorem newRaft_post_init (hs : raftpb.HardState) (s : NState) :
    HsEmpty hs →
    (NStateWf s ∧
     s.term = hs.Term' ∧
     s.vote = hs.Vote' ∧
     s.lead = W64 0 ∧ s.role = .follower ∧
     s.votes = ∅ ∧ s.outbox = []) →
    s.logst.prev = entryID.mk (W64 0) (W64 0) →
    s.logst.sents = [] →
    s.logst.uents = [] →
    s.logst.committed = W64 0 →
    NStateRel s initPState := by
  intro ⟨HT, HV, _⟩ ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ Hp Hse Hue Hc
  refine ⟨?_, Hwf⟩
  simp [toPState, initPState, Ht, Hv, HT, HV, Hl, Hr, Hvs, Ho, Hp, Hse, Hue, Hc, proleRole]

end newRaft_post

end EtcdGrove
end Perennial

/-! The trust base of the top-level results, printed in the build log. -/
#print axioms Perennial.EtcdGrove.raft.wp_Step
#print axioms Perennial.EtcdGrove.RawNode.wp_Propose
#print axioms Perennial.EtcdGrove.wp_newRaft
#print axioms Perennial.EtcdGrove.RawNode.wp_Ready
#print axioms Perennial.EtcdGrove.RawNode.wp_Advance
#print axioms Perennial.EtcdGrove.RawNode.wp_HasReady
#print axioms Perennial.EtcdGrove.RawNode.wp_Campaign
#print axioms Perennial.EtcdGrove.RawNode.wp_Step
