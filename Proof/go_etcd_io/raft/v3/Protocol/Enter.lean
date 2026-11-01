/-
# Entering a batch, restarting and stopping a node (2026-10-31, durability stage I-1)

`notes/raft-durability-proof-plan.md`, I-1, as amended by its review 1. The lemmas that move a
node's promises between its volatile half (`ownRaftGhost`), its slot (`slotInv`, `raftIdSlot`) and its
durable half (`ownDurGhost`, `raftState`'s sealed body), all defined in `Protocol/GhostState.lean`:

- `ownRaftGhost_cut`, at a `Ready`: the outbox drained (as `ownRaftGhost_drain`), the promises made
  since the last cut queued in the slot as a batch entering `S'` (`pendBatch`), the drained
  messages' facts behind the batch's fragments.
- `raft_enter`, when the client enters the batch: its promises minted in the authorities, the
  durable half moved to `S'`, the batch's fragments out (which release the drained messages).
- `raft_restart`, `raft_start_boot`: a node's volatile half built from the durable half and the
  vacant slot (R8: the durable half given back), at a restart from storage at a base `b` and commit
  `c` (`restartP`), or at a cluster's bootstrap (`bootPState`).
- `raft_stop`: the volatile half and the whole generation give back the vacant slot, the
  generation bumped (R8), so that a batch cut and not entered is dead.
- R4's restart lemmas: `S.commit`'s certificate at a lower stored commit, and the agreement of the
  acknowledgements of `S.term` above it, from Leader Completeness.

Statements only: the proofs are stage II's (`-- PORT(durability stage II)`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section enter
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The slot invariant is inside raft's namespace. -/
theorem slotN_raftN (γ : RaftNames) (id : w64) : (↑(slotN γ id) : CoPset) ⊆ ↑(raftN γ) := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- The slot invariant opens inside a ghost step (the commit invariant's registry half open). -/
theorem slotN_sub (γ : RaftNames) (id : w64) :
    (↑(slotN γ id) : CoPset) ⊆ ⊤ \ ↑(raftRegN γ) := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- The state a node restarts in from a storage holding `S` from the base `b` with the commit
index `c`: a follower of `S.term`, with `S`'s vote, no leader, an empty tally and outbox. -/
def restartP (S : RaftState) (b : entryID) (c : w64) : PState :=
  { initPState with term := S.term, vote := S.vote, base := b, log := S.entsFrom b, commit := c }

/-- **The cut** (at a `Ready`, `InvRawnodeReady`'s handout, beside `ownRaftGhost_drain`): the outbox
drained to `o'`, its messages `out` with their read credits and tickets, and the promises made since
the last cut queued in generation `g`'s free slot, as a batch entering `S'` -- the cut state's term,
vote and commit, its full log (`DurFull`, given the node's full prefix `fp`) -- with the node's
virtual maps `W`, behind whose fragments the drained messages' facts are. -/
theorem ownRaftGhost_cut (E : CoPset) (γ : RaftNames) (id : w64) (s : PState) {md : Bool}
    (q : Qp) (g : Nat) (S' : RaftState) (o' out : List Msg) :
    ↑(slotN γ id) ⊆ E →
    (o' ++ out).Perm s.outbox →
    S'.term = s.term → S'.vote = s.vote → S'.commit = s.commit →
    ⊢ (□ ∀ fp, ⌜FullOk s.base fp⌝ -∗ logRecs (GF := GF) γ base0 fp -∗ ⌜DurFull S' (fp ++ s.log)⌝) -∗
      slotLive γ id q g -∗ slotFree γ id g -∗ ownRaftGhost γ id s md ={E}=∗
      slotLive γ id q g ∗ ∃ W, pendBatch γ id g S' W ∗
        ownRaftGhost γ id { s with outbox := o' } md ∗
        ([∗list] m ∈ out, □ (durFrags γ id W -∗ isMessage γ m)) ∗
        rdCred γ (rdCount s.outbox - rdCount o') ∗ msgsTks γ out := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **Entering a batch** (the client's *enter*, under the node's generation): its promises minted
in order in the authorities (`vote_insert`, `ghost_map_insert_persist` of the acknowledgements,
campaign records and vote-time logs, the event history's appends), from their justifications; the
durable half moved to the batch's state; the batch's fragments out, which discharge its drained
messages' wands; the generation's queue free again. -/
theorem raft_enter (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (q : Qp) (g : Nat)
    (S' : RaftState) (W : DurMaps) :
    ↑(raftN γ) ⊆ E →
    ⊢ ownDurGhost (GF := GF) γ id S -∗ slotLive γ id q g -∗ pendBatch γ id g S' W ={E}=∗
      ownDurGhost γ id S' ∗ slotLive γ id q g ∗ slotFree γ id g ∗ durFrags γ id W := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **R4, the commit at a restart**: `S.commit`'s certificate gives one of a lower stored commit
`c` at a base `b` within `S`'s log, at `S.term` (in `S`'s full log, as the restarted node's). -/
theorem durPers_restart_commit (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps)
    (b : entryID) (c : w64) :
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ⊢ durPers (GF := GF) γ id S Ed -∗
      ∃ fp, ⌜FullOk b fp⌝ ∗ logRecs γ base0 fp ∗ logRecs γ b (S.entsFrom b) ∗ baseOk γ b ∗
        commitIn γ (fp ++ S.entsFrom b) c S.term ∗
        isCommitted γ ((fp ++ S.entsFrom b).take (uint.Z c).toNat) := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **R4, the acknowledgements at a restart**: every acknowledgement of `S.term` above a lower
stored commit `c` agrees with the restarted log -- above `S.commit` by `durPers`, in
`(c, S.commit]` by Leader Completeness (the committed prefix is in the log of `S.term`'s leader,
whose log the acknowledgement's `ackIn` names). -/
theorem durPers_restart_acks (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps)
    (b : entryID) (c : w64) :
    ↑(raftN γ) ⊆ E →
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ⊢ durPers (GF := GF) γ id S Ed -∗ durFrags γ id Ed ={E}=∗
      [∗map] k ↦ _u ∈ Ed.acks, ∀ (_ : k.1 = S.term ∧ uint.Z c < uint.Z k.2),
        ackAgree γ b (S.entsFrom b) k.1 k.2 := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **A restart** (in `RestartNode`, when its update fires; R8: the durable half given back,
unchanged): the vacant slot and the durable half at `S` give the volatile half of a follower of
`S.term` restarted from a storage holding `S` from the base `b` with the commit `c`
(`restartP`: `kl` forgotten, the durable `kd` taken; an empty outbox and tally), with the whole
generation and its free queue slot. Amendment 1: the bootstrap log within the stored commit. -/
theorem raft_restart (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) {md : Bool}
    (b : entryID) (c : w64) :
    ↑(raftN γ) ⊆ E →
    γ.reDyn.isSome = md →
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    (γ.reBoot.length : Int) ≤ uint.Z c →
    ⊢ ownDurGhost (GF := GF) γ id S -∗ raftIdSlot γ id ={E}=∗
      ownDurGhost γ id S ∗ ownRaftGhost γ id (restartP S b c) md ∗
      ∃ g, slotLive γ id 1 g ∗ slotFree γ id g := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **A first start from the bootstrap log** (`StartNode`, I-7): a node that has stored nothing
starts at the cluster's bootstrap state (`bootPState`: term `1`, the bootstrap log committed), which
its first `Ready` writes. -/
theorem raft_start_boot (E : CoPset) (γ : RaftNames) (id : w64) {md : Bool} :
    ↑(raftN γ) ⊆ E →
    γ.reDyn.isSome = md →
    ⊢ ownDurGhost (GF := GF) γ id RaftState.init -∗ raftIdSlot γ id ={E}=∗
      ownDurGhost γ id RaftState.init ∗ ownRaftGhost γ id (bootPState γ.reBoot) md ∗
      ∃ g, slotLive γ id 1 g ∗ slotFree γ id g := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **A stop** (R8; review 1's N6: the read credits and proposal tickets the volatile half holds
are dropped): the volatile half and the whole generation give back the vacant slot -- the
leader-side authorities with their keys' campaigns, the virtual maps reset to the entered ones --
with the generation bumped, so that a batch cut in it and not entered can no longer be. -/
theorem raft_stop (E : CoPset) (γ : RaftNames) (id : w64) (s : PState) {md : Bool} (g : Nat) :
    ↑(raftN γ) ⊆ E →
    ⊢ slotLive (GF := GF) γ id 1 g -∗ ownRaftGhost γ id s md ={E}=∗ raftIdSlot γ id := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

end enter

end EtcdGrove
end Perennial
