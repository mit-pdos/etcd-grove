/-
Port of election_proof/protocol.v, lines 4018–4494 at feb5c73d4: Leader Completeness over
the vote table, the agreement of commit facts, firing the proposal registry, committing
(`commit_extend`). (On top of `Protocol/StepGhost.lean`; the refinement obligation is
`Protocol/Refinement.lean`.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker.
* No lemma here starts with a definition's name, so all keep their Rocq names
  (`lc_core`, `cq_agree`, `fire_one`, `commit_extend`, ...). Rocq `Local Lemma`s are
  public theorems.
* `lc_core`'s `uint.Z T < k` with `k : nat` is `uint.Z T < (k : Int)`; `S m` is `m + 1`.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.StepGhost

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-! ### Leader Completeness, over the vote table (2026-10-05)

The pivot argument of Leader Completeness (`lc_core`) needs, of the voter in both the
commit quorum and the election quorum, its vote record and the history of its
acknowledgement at the time it voted. Since 2026-10-05 both are reachable without that
voter's ghost state: the vote record from the vote table in `raftCommitInv`
(`votesTbl_just`), the history from the two event-history facts (`ev_pair`). So
`lc_core` and the agreement of two commit facts (`cq_agree`) need only the table --
which `Step.commit` has, inside the invariant, and which is what lets the global
committed log be extended there. -/

omit [FfiSyntax] in
theorem quorums_intersect_cfg (cfg q1 q2 : GSet w64) :
    IsQuorum cfg q1 → IsQuorum cfg q2 → ∃ x, x ∈ q1 ∧ x ∈ q2 ∧ x ∈ cfg := by
  -- PORT: proof
  sorry

/-- A campaign log ends at its last entry. -/
theorem camp_last (T : w64) (F0 : List raftpb.Entry) :
    CampOk T F0 →
    plogTermAt base0 F0 (W64 (plogLastIndexZ base0 F0))
    = some (plogLast base0 F0).term' := by
  -- PORT: proof
  sorry

/-- What the vote table says of a vote and an earlier acknowledgement of the same voter:
its log when it voted, at least as up to date as the candidate's campaign log, and the
acknowledgement's history then (`ev_pair`). Since 2026-10-05; before, the voter's own
ghost state (`own_raft_ghost_voter`, `cluster_voter`). -/
theorem tbl_voter (γ : RaftElectionNames) (v T c t i : w64) :
    uint.Z t < uint.Z T → 0 < uint.Z i →
    ⊢ votesTbl (GF := GF) γ -∗ isVote γ v T c -∗ isAcked γ v t i -∗
      ∃ d Fv Fc, isCamp γ c T Fc ∗ logRecs γ base0 Fv ∗
        ⌜PlogWf base0 Fv ∧ plogUpToDate base0 Fv (plogLast base0 Fc) = true⌝ ∗
        hist γ Fv t i (vbnd T d) ∗
        (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) := by
  -- PORT: proof
  sorry

/-- The core of Leader Completeness, by strong induction on the term `T` of the leader
(`k` bounds it). If a quorum acknowledged the leader of `t < T` up to `n`, where its log
`F` has an entry of term `t`, then every full log `G` with records that reaches the last
entry of the campaign log of `T`'s leader has term `t` at `n`.

The election quorum of `T` and the acknowledgement quorum of `t` meet in a voter `v`:
its log `Fv` when it voted had `t` at `n` (its history of the acknowledgement, every
log it mentions agreeing with `F` below `n` by the induction hypothesis), and the
campaign log of `T` was at least as up to date. Same last term: `G` has that term down
to `Fv`'s last index (`recs_chain`), so it matches `Fv` there and below. A later last
term `tc`: `G` has `tc`'s campaign log's last entry (`recs_chain`), and the induction
hypothesis at `tc` applies to `G` itself. -/
theorem lc_core (γ : RaftElectionNames) (k : Nat) :
    ∀ (T t n : w64) (F : List raftpb.Entry) (c : w64) (F0 G : List raftpb.Entry),
    uint.Z T < (k : Int) → uint.Z t < uint.Z T →
    PlogWf base0 G →
    plogTermAt base0 G (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ isLeader γ c T -∗ isCamp γ c T F0 -∗
      logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  -- PORT: proof
  sorry

/-- Two commit facts agree below the earlier one's index: same term, the leader's logs
agree; an earlier term, `lc_core` puts the earlier committed log's entry in the later
leader's log. -/
theorem cq_lt_agree (γ : RaftElectionNames) (t1 n1 t2 n2 : w64) (G1 G2 : List raftpb.Entry) :
    uint.Z t1 < uint.Z t2 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z n1 → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  -- PORT: proof
  sorry

theorem cq_agree (γ : RaftElectionNames) (t1 n1 t2 n2 i : w64) (G1 G2 : List raftpb.Entry) :
    uint.Z i ≤ uint.Z n1 → uint.Z i ≤ uint.Z n2 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z i → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  -- PORT: proof
  sorry

/-! Firing the registry as the global log grows by one entry `e`, the entry at position
`m` of a full log `G` with records. A slot not at `e`'s `(term, index)` is unaffected:
the global log changes only at `e`'s index, where its term is another (`slot_keep`). The
slot at `e`'s `(term, index)`, if any, is the proposal of `e` (both are the leader's
entry there, `isEntry_agree`): pending, its update runs with the authority of the
extended log and its result is stored (`fire_one`). -/

omit [FfiSyntax] in
theorem take_S_lookup_ne {A : Type _} (G : List A) (m p : Nat) (e : A) :
    G[m]? = some e → p ≠ m → (G.take (m + 1))[p]? = (G.take m)[p]? := by
  -- PORT: proof
  sorry

theorem slot_keep (γ : RaftElectionNames) (k : w64 × w64) (v : PropRec) (G : List raftpb.Entry)
    (m : Nat) (e : raftpb.Entry) :
    G[m]? = some e → uint.Z e.Index' = (m : Int) + 1 →
    0 < uint.Z k.2 →
    k ≠ (e.Term', e.Index') →
    ⊢ ▷ propSlot (GF := GF) γ k v (G.take m) -∗ ▷ propSlot γ k v (G.take (m + 1)) := by
  -- PORT: proof
  sorry

theorem fire_one (γ : RaftElectionNames) (E : CoPset) (G : List raftpb.Entry) (m : Nat)
    (e : raftpb.Entry) (R : GMap (w64 × w64) PropRec) :
    PlogWf base0 G → G[m]? = some e →
    ⊢ logRecs (GF := GF) γ base0 G -∗ ownCommitted γ (G.take m) -∗ propsIdx γ R -∗
      ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take m)) ={E}=∗
      ownCommitted γ (G.take (m + 1)) ∗ ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take (m + 1))) := by
  -- PORT: proof
  sorry

theorem fire_upto (γ : RaftElectionNames) (E : CoPset) (G : List raftpb.Entry)
    (R : GMap (w64 × w64) PropRec) (d m : Nat) :
    PlogWf base0 G → m + d ≤ G.length →
    ⊢ logRecs (GF := GF) γ base0 G -∗ ownCommitted γ (G.take m) -∗ propsIdx γ R -∗
      ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take m)) ={E}=∗
      ownCommitted γ (G.take (m + d)) ∗ ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take (m + d))) := by
  -- PORT: proof
  sorry

/-- Committing: a new commit fact `cq γ t n G` extends the global log to `G`'s first `n`
entries, or finds it already past them. Inside the invariant, the global log is the
first `n0` entries of the log `G0` of an earlier commit fact; the two commit facts agree
below both (`cq_agree`, from the vote table), so -- the logs having records -- the two
prefixes are prefixes of one another (`full_take_eq`). The extension is entry by entry,
firing the registered proposals (`fire_upto`). -/
theorem commit_extend (γ : RaftElectionNames) (E : CoPset) (t n : w64) (G : List raftpb.Entry) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv (GF := GF) γ -∗ cq γ t n G ={E}=∗ isCommitted γ (G.take (uint.Z n).toNat) := by
  -- PORT: proof
  sorry

/-- A vote, recorded in the node's half of its vote map and in the table. -/
theorem vote_insert (γ : RaftElectionNames) (id : w64) (γv : GName) (voted : GMap w64 w64)
    (T c : w64) :
    γ.reVotes !! id = some γv → voted !! T = none →
    ⊢ raftCommitInv (GF := GF) γ -∗ voteJust γ id T c -∗ ghostMapAuth γv (1 : Qp).half voted ={⊤}=∗
      ghostMapAuth γv (1 : Qp).half (<[T := c]> voted) ∗ T ↪[γv]□ c := by
  -- PORT: proof
  sorry

end ghost

end EtcdGrove
end Perennial
