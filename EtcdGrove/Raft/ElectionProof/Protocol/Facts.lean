/-
Port of election_proof/protocol.v, lines 6251–7096 at feb5c73d4: the protocol facts the
code needs, replication safety (Log Matching), the global committed log from a node,
State Machine Safety, Leader Completeness, registering and collecting proposals,
allocation, and the derived conveniences used by `Election.lean`. (On top of
`Protocol/Refinement.lean`; the last module of the ghost part.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker.
* Names: `init_pstate` → `initPState` (as in the old `Protocol.lean`), `ents_rec` →
  `entsRec`; lemmas `own_raft_ghost_*` → `ownRaftGhost_*`, `own_log_ghost_within` →
  `ownLogGhost_within`, `commit_in_leader` → `commitIn_leader`; the rest keep their Rocq
  names (`heartbeat_commit_le_last`, `log_matching`, `state_machine_safety`,
  `leader_completeness`, `register_props`, `prop_collect`, `alloc_maps`, ...). Rocq
  `Local Lemma`s are public.
* `[∗ list] e;Q ∈ ents;Qs, P` is `[∗list] e;Q ∈ ents;Qs, P` (`bigSepL2`).
* `alloc_maps`'s `{K V} `{Countable K}` is `{K V : Type} [DecidableEq K]
  [Pos.Countable K] [Pos.Countable V]`: Perennial's Lean `ghostMapAuth` stores the
  encoding of the values too (Rocq's `ghost_map` stores them in `agree (leibnizO V)`).
* Rocq's `let s' := … in` in `own_raft_ghost_step_propose_reg`'s statement is inlined;
  `word.add (word.add (plast_index s) (W64 1)) (W64 k)` is `plastIndex s + W64 1 + W64 k`
  (`stamp`'s index); chained `a < b ≤ c` in a premise is `a < b ∧ b ≤ c`.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.Refinement

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-! ### Protocol facts the code needs

Each is a `Panicf` in the replication code that is dead only by protocol reasoning
(notes/raft-replication-model.md, "Protocol facts the code needs"). A callee's spec takes
the fact as a premise; `Step` derives it here, from the node's ghost state and the
incoming message.

**The message may be of a higher term** (since 2026-10-02): `Step` holds the ghost state
at the state *before* its term preamble, and a message from a later term makes the node
step down first (`becomeFollower` keeps the log and the commit index), so each lemma is
stated for `ps.term ≤ m.term` rather than equality. A stale message (`m.term < ps.term`)
is dropped by the preamble and needs none of them, except `app_recv_wf`, which holds of
any `app` (`isMessage` carries it). All four are proved (the last two since 2026-10-02,
from the acknowledgement invariant `acksOk` and from arithmetic). -/

/-- `handleHeartbeat`'s `commitTo(m.Commit)` panics if `lastIndex() < m.Commit`. It does
not: the leader sends `Commit ≤ pr.Match`, and `isMessage` carries the receiver's
acknowledgement of `pr.Match` in `m.term`. The receiver acknowledges only at its own term
(`AcksTerm`), so for a message of a higher term `pr.Match` is `0`; at its own term (where
it is not leader -- the role premise) the acknowledgement is at most the commit index or
justified by its log (`acksOk`, `ackAgree`), and either way within it (`LogOk`). `Step`
holds the ghost state before its term preamble: hence `≤`. -/
theorem heartbeat_commit_le_last (γ : RaftElectionNames) (id : w64) (ps : PState) (m : Msg) :
    m.ty = .heartbeat →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    (m.term = ps.term → ps.role ≠ .leader) →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜uint.Z m.commit ≤ plogLastIndexZ ps.base ps.log⌝ := by
  -- PORT: proof
  sorry

/-- What `raftLog.maybeAppend` needs of a received `app`'s batch: carried by the message
(`AppPayloadOk`). No premise on the terms: it is a fact of the message alone (until
2026-10-02 it was stated for `m.term = ps.term`). -/
theorem app_recv_wf (γ : RaftElectionNames) (id : w64) (ps : PState) (m : Msg) :
    m.ty = .app →
    m.dst = id →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜PlogWf (entryID.mk m.logterm m.index) m.entries ∧
        uint.Z m.index + (m.entries.length : Int) + 1 < 2 ^ 64 ∧
        ∀ e ∈ m.entries, e.Type' = W32 0⌝ := by
  -- PORT: proof
  sorry

/-- `maybeAppend`'s `commitTo(min(committed, lastnewi))` panics if the log ends before
it: it never does (`plogMaybeAppend_last`, from the batch's `AppPayloadOk`). -/
theorem app_commit_le_lastnewi (γ : RaftElectionNames) (id : w64) (ps : PState) (m : Msg)
    (lastnewi : w64) (es' : List raftpb.Entry) :
    m.ty = .app →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    plogMaybeAppend ps.base ps.log
      (entryID.mk m.logterm m.index) m.entries
      = some (lastnewi, es') →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜uint.Z lastnewi ≤ plogLastIndexZ ps.base es'⌝ := by
  -- PORT: proof
  sorry

/-- `maybeAppend` panics if the first conflicting index is at or below the commit index
(`ci ≤ l.committed`). Under `maybeAppend`'s caller's premise `committed ≤ m.Index` that is
arithmetic: a conflict is the index of one of the batch's entries, which are at
`m.Index + 1` and above (`AppPayloadOk`). (Until 2026-10-02 this was admitted as a
consequence of Leader Completeness; the premise makes it local. The term premise is not
needed.) -/
theorem app_no_conflict_below_commit (γ : RaftElectionNames) (id : w64) (ps : PState) (m : Msg) :
    m.ty = .app →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    uint.Z ps.commit ≤ uint.Z m.index →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜PlogMatches ps.base ps.log
          (entryID.mk m.logterm m.index) →
        plogFindConflict ps.base ps.log m.entries = W64 0 ∨
        uint.Z ps.commit
        < uint.Z (plogFindConflict ps.base ps.log m.entries)⌝ := by
  -- PORT: proof
  sorry

/-! ### Replication safety

The three properties replication is for, as entailments between the ghost states of
nodes. Log Matching is proved (2026-10-02) from two nodes' ghost state. Leader
Completeness and State Machine Safety are proved (2026-10-03) over the whole cluster:
see the next subsection. -/

/-- A node's log and its records. -/
theorem ownRaftGhost_log (γ : RaftElectionNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜LogOk s⌝ ∗ logRecs γ s.base s.log := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iapply ownLogGhost_recs $$ Hlg

/-- Log Matching: two logs that have the same term at an index agree on every entry up to
it (above both bases). Proved since 2026-10-02 from the two logs' records alone
(`logRecs_agree`, `plog_match_down`): entries at one (term, index) are one entry with one
predecessor term, because the term log of that term's (unique) leader says so. -/
theorem log_matching (γ : RaftElectionNames) (id1 id2 : w64) (s1 s2 : PState) (i t : w64) :
    plogTermAt s1.base s1.log i = some t →
    plogTermAt s2.base s2.log i = some t →
    ⊢ ownRaftGhost (GF := GF) γ id1 s1 -∗ ownRaftGhost γ id2 s2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z i →
          uint.Z s1.base.index' < uint.Z j →
          uint.Z s2.base.index' < uint.Z j →
          plogEntryAt s1.base s1.log j =
          plogEntryAt s2.base s2.log j⌝ := by
  -- PORT: proof
  sorry

/-! ### The global committed log, from a node (2026-10-05)

A node's committed prefix -- the first `commit` entries of its full log, the compacted
prefix `fp` (determined by the base, `FullOk_unique`) followed by the stored entries --
is a prefix of the global committed log. This is what the implementation side reads off
a node's ghost state (for `Ready`'s committed entries, ultimately). -/

theorem ownRaftGhost_inv (γ : RaftElectionNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ raftCommitInv γ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iapply ownLogGhost_inv $$ Hlg

theorem ownRaftGhost_committed (γ : RaftElectionNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗
      ∃ fp, ⌜FullOk s.base fp⌝ ∗
            isCommitted γ ((fp ++ s.log).take (uint.Z s.commit).toNat) := by
  -- PORT: proof
  sorry

/-- The entry at index `i` of a log, read in its full log. -/
theorem entry_at_full (b : entryID) (fp es : List raftpb.Entry) (i : w64) :
    FullOk b fp → uint.Z b.index' < uint.Z i →
    plogEntryAt b es i = (fp ++ es)[(uint.Z i - 1).toNat]? := by
  -- PORT: proof
  sorry

/-- **State Machine Safety**: two nodes agree on every index both have committed (above
both compaction boundaries). Since 2026-10-05 over two nodes' ghost states, not the
whole cluster: each node's committed prefix is a prefix of the global committed log
(`ownRaftGhost_committed`, `isCommitted_agree`). -/
theorem state_machine_safety (γ : RaftElectionNames) (id1 : w64) (ps1 : PState) (id2 : w64)
    (ps2 : PState) (i : w64) :
    uint.Z i ≤ uint.Z ps1.commit →
    uint.Z i ≤ uint.Z ps2.commit →
    uint.Z ps1.base.index' < uint.Z i →
    uint.Z ps2.base.index' < uint.Z i →
    ⊢ ownRaftGhost (GF := GF) γ id1 ps1 -∗ ownRaftGhost γ id2 ps2 -∗
      ⌜plogEntryAt ps1.base ps1.log i =
        plogEntryAt ps2.base ps2.log i⌝ := by
  -- PORT: proof
  sorry

/-! ### Leader Completeness (2026-10-03; over two nodes since 2026-10-05)

An entry a node has committed, at a term no later than a leader's, is in the leader's
log. The pivot argument (`lc_core`) needs the vote table, which is in the invariant: the
statement is a fancy update. (Until 2026-10-05 it was stated over the whole cluster,
`cluster_ghost`, because the pivot voter's records were in its own ghost state.) -/

/-- A leader's current log is at least as long as every log of its term (`leadFull`): the
entries it created are in its term log, whose indices are within its log
(`leadLogOwn`). -/
theorem ownLogGhost_within (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (G : List raftpb.Entry) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ leadFull γ s.term G -∗ ownLogGhost γ id s kl -∗
      ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ s.base s.log⌝ := by
  -- PORT: proof
  sorry

/-- What a leader has: its full log, with records, which extends its campaign log and is
a `leadFull` of its term; and every log of its term is within it. -/
theorem node_leader (γ : RaftElectionNames) (id2 : w64) (ps2 : PState) :
    ps2.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id2 ps2 -∗
      ∃ fp2 F0, ⌜FullOk ps2.base fp2 ∧ PlogWf ps2.base ps2.log ∧
                  F0 <+: fp2 ++ ps2.log⌝ ∗
        logRecs γ base0 fp2 ∗ logRecs γ ps2.base ps2.log ∗
        isLeader γ id2 ps2.term ∗ isCamp γ id2 ps2.term F0 ∗
        leadFull γ ps2.term (fp2 ++ ps2.log) := by
  -- PORT: proof
  sorry

theorem node_within (γ : RaftElectionNames) (id2 : w64) (ps2 : PState) (G : List raftpb.Entry) :
    ps2.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id2 ps2 -∗ leadFull γ ps2.term G -∗
      ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ ps2.base ps2.log⌝ := by
  -- PORT: proof
  sorry

/-- A full log's committed prefix, at a term no later than a leader's, is in the leader's
full log: in its campaign log by `lc_core` for an earlier term, in its log of the same
term otherwise. -/
theorem commitIn_leader (γ : RaftElectionNames) (Fn : List raftpb.Entry) (c tm id2 : w64)
    (ps2 : PState) :
    ps2.role = .leader →
    uint.Z tm ≤ uint.Z ps2.term →
    PlogWf base0 Fn →
    ⊢ votesTbl (GF := GF) γ -∗ ownRaftGhost γ id2 ps2 -∗ commitIn γ Fn c tm -∗
      logRecs γ base0 Fn -∗
      ∃ fp2, ⌜FullOk ps2.base fp2 ∧ PlogWf ps2.base ps2.log ∧
               ∀ j : w64, uint.Z j ≤ uint.Z c →
                 plogTermAt base0 Fn j = plogTermAt base0 (fp2 ++ ps2.log) j⌝ ∗
        logRecs γ base0 (fp2 ++ ps2.log) := by
  -- PORT: proof
  sorry

/-- A node's full log, its commit fact and its records. -/
theorem node_full (γ : RaftElectionNames) (id : w64) (ps : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗
      ∃ fp, ⌜FullOk ps.base fp ∧ PlogWf ps.base ps.log ∧ LogOk ps⌝ ∗
        logRecs γ base0 (fp ++ ps.log) ∗
        commitIn γ (fp ++ ps.log) ps.commit ps.term := by
  -- PORT: proof
  sorry

/-- Entries of two full logs with records, at an index above both bases, that have the
same term there, are the same entry. -/
theorem full_entry_eq (γ : RaftElectionNames) (b1 : entryID) (fp1 es1 : List raftpb.Entry)
    (b2 : entryID) (fp2 es2 : List raftpb.Entry) (i : w64) :
    FullOk b1 fp1 → FullOk b2 fp2 → PlogWf b1 es1 → PlogWf b2 es2 →
    uint.Z b1.index' < uint.Z i → uint.Z b2.index' < uint.Z i →
    (plogTermAt base0 (fp1 ++ es1) i).isSome →
    plogTermAt base0 (fp1 ++ es1) i = plogTermAt base0 (fp2 ++ es2) i →
    ⊢ logRecs (GF := GF) γ base0 (fp1 ++ es1) -∗ logRecs γ base0 (fp2 ++ es2) -∗
      ⌜plogEntryAt b1 es1 i = plogEntryAt b2 es2 i⌝ := by
  -- PORT: proof
  sorry

/-- An entry of the stored log is a term of the full log there. -/
theorem entry_term (b : entryID) (fp es : List raftpb.Entry) (i : w64) :
    FullOk b fp → uint.Z b.index' < uint.Z i ∧ uint.Z i ≤ plogLastIndexZ b es →
    (plogTermAt base0 (fp ++ es) i).isSome := by
  -- PORT: proof
  sorry

theorem leader_completeness_tbl (γ : RaftElectionNames) (id1 : w64) (ps1 : PState) (id2 : w64)
    (ps2 : PState) (i : w64) (e : raftpb.Entry) :
    uint.Z i ≤ uint.Z ps1.commit →
    plogEntryAt ps1.base ps1.log i = some e →
    ps2.role = .leader →
    uint.Z ps1.term ≤ uint.Z ps2.term →
    uint.Z ps2.base.index' < uint.Z i →
    ⊢ votesTbl (GF := GF) γ -∗ ownRaftGhost γ id1 ps1 -∗ ownRaftGhost γ id2 ps2 -∗
      ⌜plogEntryAt ps2.base ps2.log i = some e⌝ := by
  -- PORT: proof
  sorry

/-- **Leader Completeness**: an entry a node has committed, at a term no later than a
leader's, is in the leader's log (above its compaction boundary; below it the leader's
snapshot covers it). `Qed` since 2026-10-03, from `lc_core`; over two nodes since
2026-10-05. -/
theorem leader_completeness (γ : RaftElectionNames) (E : CoPset) (id1 : w64) (ps1 : PState)
    (id2 : w64) (ps2 : PState) (i : w64) (e : raftpb.Entry) :
    ↑raftN ⊆ E →
    uint.Z i ≤ uint.Z ps1.commit →
    plogEntryAt ps1.base ps1.log i = some e →
    ps2.role = .leader →
    uint.Z ps1.term ≤ uint.Z ps2.term →
    uint.Z ps2.base.index' < uint.Z i →
    ⊢ ownRaftGhost (GF := GF) γ id1 ps1 -∗ ownRaftGhost γ id2 ps2 ={E}=∗
      ownRaftGhost γ id1 ps1 ∗ ownRaftGhost γ id2 ps2 ∗
      ⌜plogEntryAt ps2.base ps2.log i = some e⌝ := by
  -- PORT: proof
  sorry

/-! ### Registering and collecting proposals (2026-10-05)

`ownRaftGhost_step_propose_reg` is `Step.propose` with the proposals' updates registered
at the `(term, index)` the leader stamps them with; the uniform `ownRaftGhost_step`
registers nothing (its `Step.propose` case is unchanged). Registration is fresh: a
registered `(t, i)` carries the entry of the leader of `t` at `i` (`propsIdx`), and the
leader of `t` has nothing in its term log past its last index
(`ownRaftGhost_term_fresh`) -- which also says the global log has no entry of term `t`
there yet, so the new slots start pending. `prop_collect` trades the client's token for
the result once its entry is committed: under two laters, one for the invariant the
result was stored in, one for the saved predicate naming it. -/

/-- A leader's term log has nothing past its last index. -/
theorem ownRaftGhost_term_fresh (γ : RaftElectionNames) (id : w64) (s : PState)
    (e : raftpb.Entry) :
    s.role = .leader →
    plogLastIndexZ s.base s.log < uint.Z e.Index' →
    e.Term' = s.term →
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ isEntry γ e -∗ False := by
  -- PORT: proof
  sorry

/-- The new entries' records, named: its persistence is one instance (the instance
search on the unfolded big separating conjunction over `stampAt` took minutes). -/
def entsRec (γ : RaftElectionNames) (t : w64) (idx : Nat → w64) (ents : List raftpb.Entry) :
    IProp GF :=
  iprop([∗list] k ↦ e ∈ ents, isEntry γ (stampAt e t (idx k)))

instance entsRec_persistent (γ : RaftElectionNames) (t : w64) (idx : Nat → w64)
    (ents : List raftpb.Entry) : Persistent (entsRec (GF := GF) γ t idx ents) := by
  unfold entsRec; infer_instance

theorem register_props (γ : RaftElectionNames) (t : w64) (idx : Nat → w64)
    (l ents : List raftpb.Entry) (Qs : List (w64 → w64 → IProp GF))
    (R : GMap (w64 × w64) PropRec) :
    Qs.length = ents.length →
    (∀ k, k < ents.length → R !! (t, idx k) = none) →
    (∀ k1 k2, k1 < ents.length → k2 < ents.length → idx k1 = idx k2 → k1 = k2) →
    (∀ k, k < ents.length → 0 < uint.Z (idx k)) →
    (∀ k e, k < ents.length → l[pos (idx k)]? = some e → e.Term' ≠ t) →
    ⊢ ghostMapAuth γ.reProps 1 R -∗ propsIdx γ R -∗
      ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v l) -∗
      entsRec γ t idx ents -∗
      ([∗list] e;Q ∈ ents;Qs, propAu γ e Q) ==∗
      ∃ R', ghostMapAuth γ.reProps 1 R' ∗ propsIdx γ R' ∗
        ([∗map] k ↦ v ∈ R', ▷ propSlot γ k v l) ∗
        [∗list] k ↦ Q ∈ Qs, ∃ γp, isProp γ t (idx k) γp Q ∗ propTok γp := by
  -- PORT: proof
  sorry

/-- `Step.propose`, registering the proposals: each update `propAu γ e Q` is registered
at the `(term, index)` its entry is stamped with, and the client gets `isProp` and the
token for it. (Rocq's `let s' := pappend s (imap …) in` is inlined.) -/
theorem ownRaftGhost_step_propose_reg (γ : RaftElectionNames) (id : w64) (s : PState)
    (ents : List raftpb.Entry) (Qs : List (w64 → w64 → IProp GF)) :
    s.role = .leader →
    plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
    Qs.length = ents.length →
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ([∗list] e;Q ∈ ents;Qs, propAu γ e Q) ={⊤}=∗
      ownRaftGhost γ id
        (psendMsgs (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))
          [pselfAck id (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))]) ∗
      [∗list] k ↦ Q ∈ Qs, ∃ γp,
        isProp γ s.term (plastIndex s + W64 1 + W64 k) γp Q ∗
        propTok γp := by
  -- PORT: proof
  sorry

/-- Collecting: once the client's entry is committed -- a committed log has an entry of
term `t` at `i` -- the token buys the result, under two laters (the invariant it was
stored in; the saved predicate). -/
theorem prop_collect (γ : RaftElectionNames) (E : CoPset) (t i : w64) (γp : GName × GName)
    (Q : w64 → w64 → IProp GF) (l : List raftpb.Entry) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv γ -∗ isProp γ t i γp Q -∗ propTok γp -∗ isCommitted γ l -∗
      ⌜∃ e, l[pos i]? = some e ∧ e.Term' = t⌝ ={E}=∗ ▷ ▷ Q t i := by
  -- PORT: proof
  sorry

/-! ### Allocation

Nothing above says the ghost state is inhabited, and an empty `ownRaftGhost` would make
every lemma here true and useless. This is what rules that out: a fresh ghost state for
any set of nodes, each in the initial protocol state -- an empty log. Since 2026-10-05 it
also allocates the commit invariant (the global committed log, empty, and the vote
table) and returns it with `isCommitted γ []`: the authority of the global log never
leaves the invariant. -/

def initPState : PState where
  term := W64 0
  vote := W64 0
  lead := W64 0
  role := .follower
  votes := ∅
  outbox := []
  base := entryID.mk (W64 0) (W64 0)
  log := []
  commit := W64 0
  matched := ∅

theorem alloc_maps {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (ids : GSet w64) :
    ⊢ |==> ∃ (names : GMap w64 GName), ⌜domSet names = ids⌝ ∗
        [∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜names !! x = some γx⌝ ∗
                               ghostMapAuth (GF := GF) γx 1 (∅ : GMap K V) := by
  -- PORT: proof
  sorry

theorem alloc_evs (ids : GSet w64) :
    ⊢ |==> ∃ (names : GMap w64 GName),
        [∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜names !! x = some γx⌝ ∗
                               monoListAuthOwn (GF := GF) γx 1 ([] : List Aev) := by
  -- PORT: proof
  sorry

theorem ownRaftGhost_alloc (E : CoPset) (cfg ids : GSet w64) :
    W64 0 ∉ ids →
    ⊢ |={E}=> ∃ γ : RaftElectionNames, ⌜γ.reCfg = cfg⌝ ∗ raftCommitInv (GF := GF) γ ∗
        isCommitted γ [] ∗
        [∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id initPState := by
  -- PORT: proof
  sorry

end ghost

/-! ## Derived conveniences used by `Election.lean` -/

section lemmas
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- Taking a step that consumes a single known message. -/
theorem ownRaftGhost_step_1 (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (s' : PState) :
    Step γ.reCfg id s [m] s' →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ={⊤}=∗
      ownRaftGhost γ id s' := by
  intro Hstep
  iintro #Hm Hown
  iapply ownRaftGhost_step γ id s [m] s' Hstep $$ [] Hown
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  iexact Hm

/-- Taking a step that consumes nothing. -/
theorem ownRaftGhost_step_0 (γ : RaftElectionNames) (id : w64) (s s' : PState) :
    Step γ.reCfg id s [] s' →
    ⊢ ownRaftGhost (GF := GF) γ id s ={⊤}=∗ ownRaftGhost γ id s' := by
  intro Hstep
  iintro Hown
  iapply ownRaftGhost_step γ id s [] s' Hstep $$ [] Hown
  iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  iempintro

end lemmas

end EtcdGrove
end Perennial
