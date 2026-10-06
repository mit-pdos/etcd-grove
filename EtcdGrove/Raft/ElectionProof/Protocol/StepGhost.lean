/-
Port of election_proof/protocol.v, lines 3199–4017 at feb5c73d4: the log ghost state
across a step. (On top of `Protocol/GhostState.lean`; Leader Completeness over the vote
table is `Protocol/LeaderCompleteness.lean`.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker.
* `kl_step` (Prop-valued) is `KlStep`. Lemma names keep the definition's name as written
  (`own_log_ghost_upd` → `ownLogGhost_upd`, `kl_ok_step` → `klOk_step`,
  `acks_ok_upd` → `acksOk_upd`, `snap_ok_message` → `snapOk_message` (the name
  `Model.lean` uses), `repl_ok_message` → `replOk_message`, `ack_agree_full` →
  `ackAgree_full`, `pleader_entry_term` → `pleaderEntry_term`); lemmas that do not
  start with a definition's name keep their snake_case name (`take_prefix_le`,
  `acks_add`, `ack_invs_insert`, `vote_excl`, `hist_replace`, ...).
* Rocq `Local Lemma`s are public theorems here (the later modules use them).
* `if kl is Some _ then true else false` is `kl.isSome`.
* Rocq's chained `a ≤ b ≤ c` in a premise is `a ≤ b ∧ b ≤ c`.
* The Rocq `Local Ltac log_mono_tac` (proof automation) is kept as a comment, for the
  proof-filling port to turn into a macro.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.GhostState

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-! ### The log ghost state across a step -/

/-- `acksOk` across a step that never lowers the term or the commit index and demotes a
leader only into a higher term. Within one term the caller says how a justification
survives the new log (`Hkeep`); across a term change there is nothing to keep: nothing
of the new term has been acknowledged yet (`AcksTerm`). -/
theorem acksOk_upd (γ : RaftElectionNames) (s s' : PState) (acks : GMap (w64 × w64) Unit) :
    uint.Z s.term ≤ uint.Z s'.term →
    (s'.role ≠ .leader → s.role = .leader →
       uint.Z s.term < uint.Z s'.term) →
    uint.Z s.commit ≤ uint.Z s'.commit →
    AcksTerm s acks →
    ⊢ □ (⌜s'.term = s.term⌝ -∗ ∀ i,
         ⌜uint.Z s'.commit < uint.Z i⌝ -∗
         ackAgree (GF := GF) γ s.base s.log s.term i -∗
         ackAgree γ s'.base s'.log s.term i) -∗
      acksOk γ s acks -∗ acksOk γ s' acks := by
  -- PORT: proof
  sorry

/- The log part of the ghost state across a step that does not make the node leader, or
keeps it leader in the same term with the same log. A leader that stops being one must
have moved to a higher term: that is what keeps it from ever allocating a second term
log for one term, and what makes its acknowledgements need no justification. The caller
supplies the new state's records, `Match` and commit facts, and how the justification
of an acknowledgement survives (`acksOk_upd`). -/
/-- How the known leader moves across a step: kept within the term (the vote only goes
from none to some, a non-leader does not become leader without `Step.win`), or reset for
a higher term. -/
def KlStep (s s' : PState) (kl kl' : Option w64) : Prop :=
  (kl' = kl ∧ s'.term = s.term ∧
   (s'.vote = W64 0 → s.vote = W64 0) ∧
   (s'.role = .leader → s.role = .leader)) ∨
  (kl' = none ∧ uint.Z s.term < uint.Z s'.term ∧
   s'.role ≠ .leader)

theorem KlStep_bnd (s s' : PState) (kl kl' : Option w64) :
    KlStep s s' kl kl' → bnd s kl ≤ bnd s' kl' := by
  intro H
  unfold bnd
  rcases H with ⟨rfl, Ht, -, -⟩ | ⟨rfl, Hlt, -⟩
  · rw [Ht]; exact Int.le_refl _
  · split <;> omega

theorem klOk_step (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl kl' : Option w64) :
    KlStep s s' kl kl' → ⊢ klOk (GF := GF) γ id s kl -∗ klOk γ id s' kl' := by
  -- PORT: proof
  sorry

theorem bnd_le (s : PState) (kl : Option w64) : bnd s kl ≤ uint.Z s.term + 1 := by
  unfold bnd; split <;> omega

theorem vbnd_bnd (s : PState) (kl : Option w64) :
    vbnd s.term kl.isSome = bnd s kl := by
  unfold vbnd bnd; cases kl <;> simp

theorem ownLogGhost_upd (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl kl' : Option w64) :
    (s'.role = .leader →
       s.role = .leader ∧ s'.term = s.term ∧
       s'.base = s.base ∧ s'.log = s.log) →
    (s'.role ≠ .leader → s.role = .leader →
       uint.Z s.term < uint.Z s'.term) →
    (s'.role = .candidate →
       s.role = .candidate ∧ s'.term = s.term) →
    uint.Z s.term ≤ uint.Z s'.term →
    uint.Z s.commit ≤ uint.Z s'.commit →
    KlStep s s' kl kl' →
    LogOk s' →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      □ (⌜s'.term = s.term⌝ -∗ ∀ i,
           ⌜uint.Z s'.commit < uint.Z i⌝ -∗
           ackAgree γ s.base s.log s.term i -∗
           ackAgree γ s'.base s'.log s.term i) -∗
      logRecs γ s'.base s'.log -∗
      matchedOk γ s' -∗
      baseOk γ s'.base -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log ∧
               TermsLe s (fp ++ s.log)⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         isCommitted γ (cprefix fp s) -∗
         ∃ fp', ⌜(FullOk s'.base fp' ∧ PlogWf s'.base s'.log ∧
                   TermsLe s' (fp' ++ s'.log)) ∧
                  (s'.role ≠ .follower → fp' ++ s'.log = fp ++ s.log)⌝ ∗
           logRecs γ base0 fp' ∗
           commitIn γ (fp' ++ s'.log) s'.commit s'.term ∗
           isCommitted γ (cprefix fp' s') ∗
           □ (∀ t i, ⌜uint.Z t ≤ uint.Z s.term⌝ -∗
                hist γ (fp ++ s.log) t i (bnd s kl) -∗
                hist γ (fp' ++ s'.log) t i (bnd s' kl'))) -∗
      ownLogGhost γ id s' kl' := by
  -- PORT: proof
  sorry

theorem ownLogGhost_recs (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ⌜LogOk s⌝ ∗ logRecs γ s.base s.log := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  isplitr; · ipureintro; exact Hlog_ok
  iexact Hrecs

/-- The full log, with what the node keeps of it. -/
theorem ownLogGhost_full (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ∃ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log ∧
              TermsLe s (fp ++ s.log)⌝ ∗
        logRecs γ base0 fp ∗
        commitIn γ (fp ++ s.log) s.commit s.term ∗
        campOwn γ id s (fp ++ s.log) := by
  -- PORT: proof
  sorry

theorem ownLogGhost_kl (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ klOk γ id s kl := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hkl

theorem ownLogGhost_wf (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ⌜PlogWf s.base s.log⌝ := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  ipureintro; exact Hfull.2.1

theorem ownLogGhost_committed (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ isCommittedIdx γ s.commit := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iapply commitIn_committed $$ Hcommit

theorem ownLogGhost_matched (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ matchedOk γ s := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hmatched

theorem ownLogGhost_base (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ baseOk γ s.base := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hbase

/-- The node's committed prefix, with the compacted prefix it is of. -/
theorem ownLogGhost_cmt (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ∃ fp, ⌜FullOk s.base fp⌝ ∗ logRecs γ base0 fp ∗ isCommitted γ (cprefix fp s) := by
  -- PORT: proof
  sorry

theorem ownLogGhost_inv (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ raftCommitInv γ := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hinv

/-- The compacted prefix is determined by the base (`FullOk_unique`), so a committed
prefix can be read with any compacted prefix that has records. -/
theorem cprefix_transfer (γ : RaftElectionNames) (fp1 fp2 : List raftpb.Entry) (s : PState) :
    FullOk s.base fp1 → FullOk s.base fp2 →
    ⊢ logRecs (GF := GF) γ base0 fp1 -∗ logRecs γ base0 fp2 -∗
      isCommitted γ (cprefix fp1 s) -∗ isCommitted γ (cprefix fp2 s) := by
  -- PORT: proof
  sorry

omit [FfiSyntax] in
theorem take_prefix_le {A : Type _} (l : List A) (n m : Nat) :
    n ≤ m → l.take n <+: l.take m := by
  intro H
  have : l.take n = (l.take m).take n := by rw [List.take_take, Nat.min_eq_left H]
  rw [this]; exact List.take_prefix _ _

/-- A log that grows past the commit index keeps its committed prefix. -/
theorem cprefix_app (fp : List raftpb.Entry) (s : PState) (es : List raftpb.Entry) :
    uint.Z s.commit ≤ ((fp ++ s.log).length : Int) →
    (fp ++ s.log ++ es).take (uint.Z s.commit).toNat = cprefix fp s := by
  -- PORT: proof
  sorry

/-- Learning the leader of the term, from one of its messages: the bound goes up to the
term plus one. The caller supplies that the node is not in the winning quorum if it has
not voted (`vote_excl`). -/
theorem ownLogGhost_learn (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (ldr : w64) (q : GSet w64) :
    s.role ≠ .leader →
    ⊢ isWin (GF := GF) γ ldr s.term q -∗ ⌜s.vote = W64 0 → id ∉ q⌝ -∗
      ownLogGhost γ id s kl -∗ ownLogGhost γ id s (some ldr) := by
  -- PORT: proof
  sorry

/-- The same, for a step that leaves the log alone. The caller says how the commit fact
moves to the new commit index. -/
theorem ownLogGhost_mono' (γ : RaftElectionNames) (id : w64) (s s' : PState)
    (kl kl' : Option w64) :
    s'.log = s.log →
    s'.base = s.base →
    (s'.role = .leader →
       s.role = .leader ∧ s'.term = s.term) →
    (s'.role ≠ .leader → s.role = .leader →
       uint.Z s.term < uint.Z s'.term) →
    (s'.role = .candidate →
       s.role = .candidate ∧ s'.term = s.term) →
    uint.Z s.term ≤ uint.Z s'.term →
    uint.Z s.commit ≤ uint.Z s'.commit →
    KlStep s s' kl kl' →
    (s'.commit = s.commit ∨
     uint.Z s'.commit ≤ plogLastIndexZ s.base s.log) →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ matchedOk γ s' -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         commitIn γ (fp ++ s.log) s'.commit s'.term) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         isCommitted γ (cprefix fp s) -∗ isCommitted γ (cprefix fp s')) -∗
      ownLogGhost γ id s' kl' := by
  -- PORT: proof
  sorry

/-- The same, when `Match` and the commit index do not change either, at the same
term ... -/
theorem ownLogGhost_mono (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl : Option w64) :
    s'.log = s.log →
    s'.base = s.base →
    s'.commit = s.commit →
    (s'.role = .leader →
       s.role = .leader ∧ s'.term = s.term ∧
       s'.matched = s.matched) →
    (s'.role = .candidate →
       s.role = .candidate ∧ s'.term = s.term) →
    (s.role = .leader → s'.role = .leader) →
    s'.term = s.term →
    (s'.vote = W64 0 → s.vote = W64 0) →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ownLogGhost γ id s' kl := by
  -- PORT: proof
  sorry

/-- ... or at a higher term, where the known leader is forgotten. -/
theorem ownLogGhost_mono_up (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl : Option w64) :
    s'.log = s.log →
    s'.base = s.base →
    s'.commit = s.commit →
    s'.role = .follower →
    uint.Z s.term < uint.Z s'.term →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ownLogGhost γ id s' none := by
  -- PORT: proof
  sorry

/- Discharging `ownLogGhost_mono`'s premises for a concrete step. Rocq:
```
Local Ltac log_mono_tac :=
  first [ (rewrite /kl_step; left; split_and!; [reflexivity|..]; simpl; intros;
           first [ done | congruence ])
        | (rewrite ?pbecome_follower_vote_same; intros; done)
        | (simpl; intros; first [ done | congruence | lia | word | (split_and!; done) ]) ].
```
-/

/-- Adding an acknowledgement to one's own map: fresh, or already there. -/
theorem acks_add (γa : GName) (acks : GMap (w64 × w64) Unit) (k : w64 × w64) :
    ⊢ ghostMapAuth (GF := GF) γa 1 acks -∗ ([∗map] k ↦ u ∈ acks, k ↪[γa]□ u) ==∗
      ghostMapAuth γa 1 (<[k := ()]> acks) ∗
      ([∗map] k ↦ u ∈ <[k := ()]> acks, k ↪[γa]□ u) ∗ k ↪[γa]□ () := by
  -- PORT: proof
  sorry

theorem AcksTerm_insert (s : PState) (acks : GMap (w64 × w64) Unit) (t i : w64) :
    uint.Z t ≤ uint.Z s.term → AcksTerm s acks → AcksTerm s (<[(t, i) := ()]> acks) := by
  intro Ht H k Hk
  by_cases Hkk : k = (t, i)
  · subst Hkk; exact Ht
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hkk)] at Hk; exact H k Hk

/-- The per-acknowledgement invariants of a new acknowledgement, at the node's term: its
history, and nothing for the vote-time logs (they are of terms up to this one). -/
theorem ack_invs_insert (γ : RaftElectionNames) (s : PState) (kl : Option w64)
    (F : List raftpb.Entry) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)) (i : w64) :
    ⊢ hist (GF := GF) γ F s.term i (bnd s kl) -∗
      histsOk γ s kl F acks -∗ vlogsOk γ s acks vlogs -∗
      histsOk γ s kl F (<[(s.term, i) := ()]> acks) ∗
      vlogsOk γ s (<[(s.term, i) := ()]> acks) vlogs := by
  -- PORT: proof
  sorry

/-- A node acknowledges at its own term, with the justification `acksOk` asks of it and
the history `histsOk` asks of it. -/
theorem ownLogGhost_ack (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (i : w64) :
    ⊢ ackOk (GF := GF) γ s (s.term, i) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         hist γ (fp ++ s.log) s.term i (bnd s kl)) -∗
      ownLogGhost γ id s kl ==∗ ownLogGhost γ id s kl ∗ isAcked γ id s.term i := by
  -- PORT: proof
  sorry

theorem pleaderEntry_term (s : PState) : (pleaderEntry s).Term' = s.term := rfl

/-- A leader's whole log is a log of the leader of its term, with its full log and the
commit fact about it. -/
theorem ownLogGhost_lead_full (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ ownLogGhost γ id s kl -∗
      (∃ fp, leadPrefix γ id s.term s.base s.log ∗
         lpfull γ id s.term s.base s.log fp ∗
         commitIn γ (fp ++ s.log) s.commit s.term) ∗
      ownLogGhost γ id s kl := by
  -- PORT: proof
  sorry

theorem ownLogGhost_lead_prefix (γ : RaftElectionNames) (id : w64) (s : PState)
    (kl : Option w64) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ ownLogGhost γ id s kl -∗
      leadPrefix γ id s.term s.base s.log ∗ ownLogGhost γ id s kl := by
  -- PORT: proof
  sorry

/-- `Step.campaign`, on the log ghost state: record the campaign log (the full log,
unchanged since) and, for the self-vote, the vote-time log -- with the histories of
every earlier acknowledgement; the new term has no known leader. -/
theorem ownLogGhost_campaign (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    s.role ≠ .leader →
    uint.Z s.term + 1 < 2 ^ 64 →
    ⊢ ownLogGhost (GF := GF) γ id s kl ==∗
      ∃ k F, ownLogGhost γ id (pbecomeCandidate id s) none ∗
        isCamp γ id (s.term + W64 1) F ∗
        isVlog γ id k (s.term + W64 1) false F ∗ logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ plogLast base0 F = plogLast s.base s.log⌝ ∗
        voteEv γ id (s.term + W64 1) false F := by
  -- PORT: proof
  sorry

/-- A first vote, on the log ghost state: record the vote-time log, which has the
histories of all acknowledgements, at the node's bound -- the term, or the term plus one
if it knows the term's leader. -/
theorem ownLogGhost_vote (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl ==∗
      ∃ k F, ownLogGhost γ id s kl ∗
        isVlog γ id k s.term kl.isSome F ∗
        logRecs γ base0 F ∗ klOk γ id s kl ∗
        ⌜PlogWf base0 F ∧
          ∀ x, plogUpToDate base0 F x = plogUpToDate s.base s.log x⌝ ∗
        voteEv γ id s.term kl.isSome F := by
  -- PORT: proof
  sorry

/-- What a leader's `MsgSnap` carries beyond its leadership. `Qed` since 2026-10-03
(admitted from 2026-10-02 as a client assumption, before `SnapOk` carried the commit
bound and the log fact): `isCommittedIdx` is `isCommittedIdx_le` of the commit index;
`isSnapMeta` is the log's record of the entry at `m.index` (`logRecs`), or, when the
snapshot is exactly at the base, `ownLogGhost`'s `baseOk`. -/
theorem snapOk_message (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    PlogWfR s.base s.log →
    SnapOk id s m →
    ⊢ isCommittedIdx (GF := GF) γ s.commit -∗
      logRecs γ s.base s.log -∗
      baseOk γ s.base -∗
      isCommittedIdx γ m.index ∗ isSnapMeta γ m.logterm m.index ∗
      ⌜plogTermAt s.base s.log m.index = some m.logterm⌝ := by
  -- PORT: proof
  sorry

/-- What a leader's broadcast carries, from what the leader holds. -/
theorem replOk_message (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (fp : List raftpb.Entry) :
    PlogWfR s.base s.log →
    ReplOk id s m → id ≠ W64 0 →
    ⊢ isLeader (GF := GF) γ id s.term -∗
      leadPrefix γ id s.term s.base s.log -∗
      lpfull γ id s.term s.base s.log fp -∗
      logRecs γ s.base s.log -∗
      commitIn γ (fp ++ s.log) s.commit s.term -∗
      baseOk γ s.base -∗
      isCommitted γ (cprefix fp s) -∗
      isMessage γ m := by
  -- PORT: proof
  sorry

/-- A full log at its commit index has the history of an acknowledgement there, at any
term at least the commit fact's. -/
theorem hist_of_commit (γ : RaftElectionNames) (F : List raftpb.Entry) (c tm : w64) (B : Int) :
    PlogWf base0 F → uint.Z tm < B →
    ⊢ logRecs (GF := GF) γ base0 F -∗ commitIn γ F c tm -∗ hist γ F tm c B := by
  -- PORT: proof
  sorry

/-- An acknowledgement justified by the log, in full-log terms. -/
theorem ackAgree_full (γ : RaftElectionNames) (b : entryID) (es fp : List raftpb.Entry)
    (t i : w64) :
    FullOk b fp → uint.Z b.index' ≤ uint.Z i →
    ⊢ ackAgree (GF := GF) γ b es t i -∗
      ∃ X, leadFull γ t X ∗
        ⌜(plogTermAt base0 X i).isSome ∧
          plogTermAt base0 X i = plogTermAt base0 (fp ++ es) i⌝ := by
  -- PORT: proof
  sorry

/- A non-leader's own acknowledgement of its term above its commit index is justified by
its log. -/
/-- A node not yet voted in its term is in no winning quorum of it. -/
theorem vote_excl (γ : RaftElectionNames) (id : w64) (s : PState) (γv : GName)
    (voted : GMap w64 w64) (ldr : w64) (q : GSet w64) :
    γ.reVotes !! id = some γv → VoteHistOk voted s →
    ⊢ ghostMapAuth (GF := GF) γv (1 : Qp).half voted -∗ isWin γ ldr s.term q -∗
      ⌜s.vote = W64 0 → id ∉ q⌝ := by
  -- PORT: proof
  sorry

theorem ownLogGhost_ack_agree (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (i : w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ isAcked γ id s.term i -∗
      ∀ (_ : s.role ≠ .leader ∧ uint.Z s.commit < uint.Z i),
        ackAgree γ s.base s.log s.term i := by
  -- PORT: proof
  sorry

/-- Histories across a log change that keeps the log below `c`, puts a leader's log `Y`
(of a term in range) on `[c, L]`, and drops what is past `L` -- where the old log
disagreed with `Y` at some `k` in `[c, L]` (the cut of `Step.appAccept`, the snapshot
index of `Step.snapRestore`). -/
theorem hist_replace (γ : RaftElectionNames) (F F' Y : List raftpb.Entry) (t i T : w64)
    (B B' c : Int) (k L : w64) :
    B ≤ B' → uint.Z t ≤ uint.Z T → uint.Z T < B' →
    0 < uint.Z k → c ≤ uint.Z k ∧ uint.Z k ≤ uint.Z L →
    (∀ j : w64, uint.Z j < c → plogTermAt base0 F' j = plogTermAt base0 F j) →
    (∀ j : w64, c ≤ uint.Z j ∧ uint.Z j ≤ uint.Z L →
       plogTermAt base0 F' j = plogTermAt base0 Y j ∧ (plogTermAt base0 Y j).isSome) →
    plogTermAt base0 F k ≠ plogTermAt base0 Y k →
    (∀ j : w64, uint.Z L < uint.Z j → plogTermAt base0 F' j = none) →
    ⊢ leadFull (GF := GF) γ T Y -∗ hist γ F t i B -∗ hist γ F' t i B' := by
  -- PORT: proof
  sorry

end ghost

end EtcdGrove
end Perennial
