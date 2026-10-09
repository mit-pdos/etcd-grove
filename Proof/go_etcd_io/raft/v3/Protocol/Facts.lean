/-
Port of election_proof/protocol.v, lines 6251–7096 at feb5c73d4: the protocol facts the
code needs, replication safety (Log Matching), the global committed log from a node,
State Machine Safety, Leader Completeness, registering and collecting proposals,
allocation, and the derived conveniences used by `Link.lean`. (On top of
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
module

public import Proof.go_etcd_io.raft.v3.Protocol.Refinement

@[expose] public section

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
theorem heartbeat_commit_le_last (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) :
    m.ty = .heartbeat →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    (m.term = ps.term → ps.role ≠ .leader) →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜uint.Z m.commit ≤ plogLastIndexZ ps.base ps.log⌝ := by
  intro Hty Hto Hle Hrole
  simp only [isMessage, Hty]
  unfold ownRaftGhost ownLogGhost isAcked
  iintro ⟨%γv, %voted, %kl, H⟩ ⟨-, -, ⟨%i, %Hci, Hack⟩, -⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  obtain ⟨-, -, Hcl⟩ := Hlog_ok
  have := plogLastIndexZ_nonneg ps.base ps.log
  icases Hack with (%H0 | ⟨⟨%γa', %Hγa', Hfrag⟩, -⟩)
  · ipureintro; omega
  rw [Hto, Haname] at Hγa'
  cases Hγa'
  icases ghost_map_lookup $$ Hacks Hfrag with %Hk
  have Hkt : uint.Z m.term ≤ uint.Z ps.term := Hacks_term _ (by rw [Hk]; rfl)
  have Heq : m.term = ps.term := by word
  have Hr := Hrole Heq
  unfold acksOk
  rcases Hr' : ps.role
  rotate_left 2
  · exact absurd Hr' Hr
  all_goals
    ihave #Hk' := BigSepM.bigSepM_lookup (Φ := fun k _ => ackOk (GF := GF) γ ps k) Hk $$ Hacks_ok
    by_cases Hlt : uint.Z ps.commit < uint.Z i
    · unfold ackOk ackAgree
      ihave ⟨%Hil, -⟩ := Hk' $$ %(⟨Heq, Hlt⟩ : (m.term, i).1 = ps.term ∧ uint.Z ps.commit < uint.Z (m.term, i).2)
      ipureintro; simp only at Hil; omega
    · ipureintro; omega

/-- What `raftLog.maybeAppend` needs of a received `app`'s batch: carried by the message
(`AppPayloadOk`). No premise on the terms: it is a fact of the message alone (until
2026-10-02 it was stated for `m.term = ps.term`). -/
theorem app_recv_wf (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) :
    m.ty = .app →
    m.dst = id →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜PlogWf (entryID.mk m.logterm m.index) m.entries ∧
        uint.Z m.index + (m.entries.length : Int) + 1 < 2 ^ 64 ∧
        ∀ e ∈ m.entries, e.Type' = W32 0⌝ := by
  intro Hty _
  simp only [isMessage, Hty]
  iintro - ⟨%Hpay, -⟩
  ipureintro; exact Hpay

/-- `maybeAppend`'s `commitTo(min(committed, lastnewi))` panics if the log ends before
it: it never does (`plogMaybeAppend_last`, from the batch's `AppPayloadOk`). -/
theorem app_commit_le_lastnewi (γ : RaftNames) (id : w64) (ps : PState) (m : Msg)
    (lastnewi : w64) (es' : List raftpb.Entry) :
    m.ty = .app →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    plogMaybeAppend ps.base ps.log
      (entryID.mk m.logterm m.index) m.entries
      = some (lastnewi, es') →
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ isMessage γ m -∗
      ⌜uint.Z lastnewi ≤ plogLastIndexZ ps.base es'⌝ := by
  intro Hty Hto _ Happ
  iintro Hown #Hm
  icases app_recv_wf γ id ps m Hty Hto $$ Hown Hm with %Hp
  obtain ⟨Hwf, Hnw, -⟩ := Hp
  ipureintro
  exact plogMaybeAppend_last _ _ _ _ _ _ Hwf Hnw Happ

/-- `maybeAppend` panics if the first conflicting index is at or below the commit index
(`ci ≤ l.committed`). Under `maybeAppend`'s caller's premise `committed ≤ m.Index` that is
arithmetic: a conflict is the index of one of the batch's entries, which are at
`m.Index + 1` and above (`AppPayloadOk`). (Until 2026-10-02 this was admitted as a
consequence of Leader Completeness; the premise makes it local. The term premise is not
needed.) -/
theorem app_no_conflict_below_commit (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) :
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
  intro Hty _ _ Hcm
  simp only [isMessage, Hty]
  iintro - ⟨%Hpay, -⟩
  ipureintro
  intro _
  obtain ⟨Hwf, -, -⟩ := Hpay
  by_cases Hne : plogFindConflict ps.base ps.log m.entries = W64 0
  · exact .inl Hne
  right
  obtain ⟨d, e, Hd, He, -, -⟩ := plogFindConflict_some _ _ _ Hne
  have := Hwf _ _ Hd
  rw [← He]
  simp only at this
  omega

/-! ### Replication safety

The three properties replication is for, as entailments between the ghost states of
nodes. Log Matching is proved (2026-10-02) from two nodes' ghost state. Leader
Completeness and State Machine Safety are proved (2026-10-03) over the whole cluster:
see the next subsection. -/

/-- A node's log and its records. -/
theorem ownRaftGhost_log (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜LogOk s⌝ ∗ logRecs γ s.base s.log := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iapply ownLogGhost_recs $$ Hlg

/-- Log Matching: two logs that have the same term at an index agree on every entry up to
it (above both bases). Proved since 2026-10-02 from the two logs' records alone
(`logRecs_agree`, `plog_match_down`): entries at one (term, index) are one entry with one
predecessor term, because the term log of that term's (unique) leader says so. -/
theorem log_matching (γ : RaftNames) (id1 id2 : w64) (s1 s2 : PState) (i t : w64) :
    plogTermAt s1.base s1.log i = some t →
    plogTermAt s2.base s2.log i = some t →
    ⊢ ownRaftGhost (GF := GF) γ id1 s1 -∗ ownRaftGhost γ id2 s2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z i →
          uint.Z s1.base.index' < uint.Z j →
          uint.Z s2.base.index' < uint.Z j →
          plogEntryAt s1.base s1.log j =
          plogEntryAt s2.base s2.log j⌝ := by
  intro H1 H2
  iintro Hs1 Hs2
  icases ownRaftGhost_log γ id1 s1 $$ Hs1 with ⟨%Hok1, #Hr1⟩
  icases ownRaftGhost_log γ id2 s2 $$ Hs2 with ⟨%Hok2, #Hr2⟩
  obtain ⟨Hwf1, -, -⟩ := Hok1
  obtain ⟨Hwf2, -, -⟩ := Hok2
  icases logRecs_agree γ _ _ _ _ $$ Hr1 Hr2 with %HRA
  ipureintro
  intro j Hji Hb1 Hb2
  have Hj := plog_match_down _ _ _ _ i Hwf1 Hwf2 HRA (by rw [H1]; rfl) (by rw [H1, H2]) j
    (by omega) (by omega) Hji
  have Hl1 := (plogTermAt_some_range _ _ _ _ H1).2
  obtain ⟨tj, Htj⟩ : ∃ tj, plogTermAt s1.base s1.log j = some tj :=
    Option.isSome_iff_exists.mp (plogTermAt_in_range _ _ _ ⟨by omega, by omega⟩)
  obtain ⟨e1, He1, Hi1, Ht1⟩ := plogTermAt_some_entry _ _ _ _ Hwf1 Htj Hb1
  rw [Hj] at Htj
  obtain ⟨e2, He2, Hi2, Ht2⟩ := plogTermAt_some_entry _ _ _ _ Hwf2 Htj Hb2
  rw [plogEntryAt_lookup _ _ _ Hb1, plogEntryAt_lookup _ _ _ Hb2, He1, He2]
  have := uint_Z_lt j
  obtain ⟨rfl, -⟩ := HRA _ _ _ _ He1 He2 (by omega) (by omega) (by rw [Ht1, Ht2])
    (by rw [Hi1, Hi2])
  rfl

/-! ### The global committed log, from a node (2026-10-05)

A node's committed prefix -- the first `commit` entries of its full log, the compacted
prefix `fp` (determined by the base, `FullOk_unique`) followed by the stored entries --
is a prefix of the global committed log. This is what the implementation side reads off
a node's ghost state (for `Ready`'s committed entries, ultimately). -/

theorem ownRaftGhost_inv (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ raftCommitInv γ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iapply ownLogGhost_inv $$ Hlg

theorem ownRaftGhost_committed (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗
      ∃ fp, ⌜FullOk s.base fp⌝ ∗
            isCommitted γ ((fp ++ s.log).take (uint.Z s.commit).toNat) := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  have Hcmt := ownLogGhost_cmt (GF := GF) γ id s kl
  unfold cprefix at Hcmt
  icases Hcmt $$ Hlg with ⟨%fp, %Hf, -, #Hc⟩
  iexists fp
  isplitr
  · ipureintro; exact Hf
  · iexact Hc

/-- The entry at index `i` of a log, read in its full log. -/
theorem entry_at_full (b : entryID) (fp es : List raftpb.Entry) (i : w64) :
    FullOk b fp → uint.Z b.index' < uint.Z i →
    plogEntryAt b es i = (fp ++ es)[(uint.Z i - 1).toNat]? := by
  intro ⟨Hlen, _, _⟩ Hi
  rw [plogEntryAt_lookup _ _ _ Hi, List.getElem?_append_right (by omega)]
  congr 1; omega

private theorem ownRaftGhost_committed_ok (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗
      ∃ fp, ⌜FullOk s.base fp ∧ LogOk s⌝ ∗
            isCommitted γ ((fp ++ s.log).take (uint.Z s.commit).toNat) := by
  unfold ownRaftGhost ownLogGhost cprefix
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexists fp
  isplitr
  · ipureintro; exact ⟨Hfull.1, Hlog_ok⟩
  · iexact Hcmt

/-- **State Machine Safety**: two nodes agree on every index both have committed (above
both compaction boundaries). Since 2026-10-05 over two nodes' ghost states, not the
whole cluster: each node's committed prefix is a prefix of the global committed log
(`ownRaftGhost_committed`, `isCommitted_agree`). -/
theorem state_machine_safety (γ : RaftNames) (id1 : w64) (ps1 : PState) (id2 : w64)
    (ps2 : PState) (i : w64) :
    uint.Z i ≤ uint.Z ps1.commit →
    uint.Z i ≤ uint.Z ps2.commit →
    uint.Z ps1.base.index' < uint.Z i →
    uint.Z ps2.base.index' < uint.Z i →
    ⊢ ownRaftGhost (GF := GF) γ id1 ps1 -∗ ownRaftGhost γ id2 ps2 -∗
      ⌜plogEntryAt ps1.base ps1.log i =
        plogEntryAt ps2.base ps2.log i⌝ := by
  intro Hi1 Hi2 Hb1 Hb2
  iintro H1 H2
  icases ownRaftGhost_committed_ok γ id1 ps1 $$ H1 with ⟨%fp1, %Hf1, #Hc1⟩
  icases ownRaftGhost_committed_ok γ id2 ps2 $$ H2 with ⟨%fp2, %Hf2, #Hc2⟩
  obtain ⟨Hf1, -, -, Hl1⟩ := Hf1
  obtain ⟨Hf2, -, -, Hl2⟩ := Hf2
  icases isCommitted_agree γ _ _ $$ Hc1 Hc2 with %Hp
  ipureintro
  rw [entry_at_full _ fp1 _ _ Hf1 Hb1, entry_at_full _ fp2 _ _ Hf2 Hb2]
  have Hlen1 := Hf1.1
  have Hlen2 := Hf2.1
  unfold plogLastIndexZ at Hl1 Hl2
  have Hk1 : (uint.Z i - 1).toNat < (uint.Z ps1.commit).toNat := by omega
  have Hk2 : (uint.Z i - 1).toNat < (uint.Z ps2.commit).toNat := by omega
  rw [← List.getElem?_take_of_lt (l := fp1 ++ ps1.log) Hk1,
    ← List.getElem?_take_of_lt (l := fp2 ++ ps2.log) Hk2]
  obtain ⟨x1, Hx1⟩ : ∃ x, ((fp1 ++ ps1.log).take (uint.Z ps1.commit).toNat)[(uint.Z i - 1).toNat]?
      = some x := ⟨_, List.getElem?_eq_getElem (by rw [List.length_take, List.length_append]; omega)⟩
  obtain ⟨x2, Hx2⟩ : ∃ x, ((fp2 ++ ps2.log).take (uint.Z ps2.commit).toNat)[(uint.Z i - 1).toNat]?
      = some x := ⟨_, List.getElem?_eq_getElem (by rw [List.length_take, List.length_append]; omega)⟩
  rw [Hx1, Hx2]
  rcases Hp with Hp | Hp
  · have := prefix_lookup_Some Hx1 Hp; rw [Hx2] at this; exact this.symm
  · have := prefix_lookup_Some Hx2 Hp; rw [Hx1] at this; exact this

/-! ### Leader Completeness (2026-10-03; over two nodes since 2026-10-05)

An entry a node has committed, at a term no later than a leader's, is in the leader's
log. The pivot argument (`lc_core`) needs the vote table, which is in the invariant: the
statement is a fancy update. (Until 2026-10-05 it was stated over the whole cluster,
`cluster_ghost`, because the pivot voter's records were in its own ghost state.) -/

/-- A leader's current log is at least as long as every log of its term (`leadFull`): the
entries it created are in its term log, whose indices are within its log
(`leadLogOwn`). -/
theorem ownLogGhost_within (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64)
    (G : List raftpb.Entry) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ leadFull γ s.term G -∗ ownLogGhost γ id s kl -∗
      ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ s.base s.log⌝ := by
  intro Hr
  unfold ownLogGhost
  iintro #Hl #HG H
  unfold leadFull leadPrefix lpfull isTermLog leadFrags
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  unfold leadLogOwn
  rw [Hr]
  icases Htlog with ⟨%γt, %M, %l0, %Hγt, Ha, -, %Hdom, %Hpre, -⟩
  icases HG with ⟨%ldr, %bL, %l, %fpG, ⟨#Hl', %γt', %l0', ⟨%γm', %Hγm', #Htf⟩, %Hwr', -, #Hlf'⟩,
    ⟨%F0, -, -, %HfG⟩, %HG⟩
  icases isLeader_unique γ id ldr s.term $$ Hl Hl' with %Hid
  subst Hid
  rw [Htname] at Hγm'
  cases Hγm'
  icases ghost_map_lookup $$ Hterms Htf with %Hlook
  rw [Hγt] at Hlook
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (γt = γt' ∧ s.base = bL) ∧ l0 = l0' := by simpa using Hlook
  subst HG
  obtain ⟨HfG, -, HwG, -⟩ := HfG
  rw [full_last_index _ _ _ HfG]
  by_cases Hle : l.length ≤ l0.length
  · have := Hpre.length_le
    ipureintro; unfold plogLastIndexZ; omega
  · obtain ⟨e, He⟩ : ∃ e, l[l.length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave He' := BigSepL.bigSepL_lookup (Φ := fun k e => if l0.length ≤ k then
        iprop(∃ pt : w64, e.Index' ↪[γt]□ ((e, pt) : raftpb.Entry × w64)) else iprop(True)) He
      $$ Hlf'
    rw [ite_eq_left (show l0.length ≤ l.length - 1 by omega)]
    icases He' with ⟨%pt, He'⟩
    icases ghost_map_lookup $$ Ha He' with %HM
    have Hd := Hdom _ (by rw [HM]; rfl)
    have Hw := HwG _ _ He
    ipureintro; unfold plogLastIndexZ at Hd ⊢; omega

/-- What a leader has: its full log, with records, which extends its campaign log and is
a `leadFull` of its term; and every log of its term is within it. -/
theorem node_leader (γ : RaftNames) (id2 : w64) (ps2 : PState) :
    ps2.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id2 ps2 -∗
      ∃ fp2 F0, ⌜FullOk ps2.base fp2 ∧ PlogWf ps2.base ps2.log ∧
                  F0 <+: fp2 ++ ps2.log⌝ ∗
        logRecs γ base0 fp2 ∗ logRecs γ ps2.base ps2.log ∗
        isLeader γ id2 ps2.term ∗ isCamp γ id2 ps2.term F0 ∗
        leadFull γ ps2.term (fp2 ++ ps2.log) := by
  intro Hr2
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  have Hw : leaderWit (GF := GF) γ id2 ps2 = isLeader γ id2 ps2.term := by
    unfold leaderWit; rw [Hr2]
  rw [Hw]
  icases ownLogGhost_lead_full γ id2 ps2 kl Hr2 $$ Hlead Hlg with ⟨⟨%fp, #Hp, #Hpf, -⟩, Hlg⟩
  icases ownLogGhost_recs γ id2 ps2 kl $$ Hlg with ⟨-, #Hr⟩
  ihave #HLF := leadFull_intro γ id2 ps2.term ps2.base ps2.log fp $$ Hp Hpf
  unfold lpfull
  icases Hpf with ⟨%F0, #Hc0, #Hfr, %Hf⟩
  obtain ⟨Hf, Hpre, Hw, -⟩ := Hf
  iexists fp, F0
  isplitr; · ipureintro; exact ⟨Hf, Hw, Hpre⟩
  iframe Hfr Hr Hlead Hc0 HLF

theorem node_within (γ : RaftNames) (id2 : w64) (ps2 : PState) (G : List raftpb.Entry) :
    ps2.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id2 ps2 -∗ leadFull γ ps2.term G -∗
      ⌜plogLastIndexZ base0 G ≤ plogLastIndexZ ps2.base ps2.log⌝ := by
  intro Hr2
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩ #HG
  iNamed H
  have Hw : leaderWit (GF := GF) γ id2 ps2 = isLeader γ id2 ps2.term := by
    unfold leaderWit; rw [Hr2]
  rw [Hw]
  iapply ownLogGhost_within γ id2 ps2 kl G Hr2 $$ Hlead HG Hlg

private theorem cq_lead (γ : RaftNames) (t n : w64) (G : List raftpb.Entry) :
    ⊢ cq (GF := GF) γ t n G -∗ ⌜plogTermAt base0 G n = some t⌝ ∗ leadFull γ t G := by
  unfold cq
  iintro ⟨%H, #Hf, -⟩
  isplitr
  · ipureintro; exact H
  · iexact Hf

/-- A full log's committed prefix, at a term no later than a leader's, is in the leader's
full log: in its campaign log by `lc_core` for an earlier term, in its log of the same
term otherwise. -/
theorem commitIn_leader (γ : RaftNames) (Fn : List raftpb.Entry) (c tm id2 : w64)
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
  intro Hr2 Htm HwFn
  iintro Htbl HS #Hc #HrFn
  ihave #⟨%fp2, %F0, %Hp, #Hfr2, #Hr2', #Hl2, #Hc0, #Hfl2⟩ := node_leader γ id2 ps2 Hr2 $$ HS
  obtain ⟨Hf2, Hw2, Hpre⟩ := Hp
  ihave #HrF2 := logRecs_full γ ps2.base fp2 ps2.log Hf2 $$ Hfr2 Hr2'
  have HwF2 := full_wf _ _ _ Hf2 Hw2
  unfold commitIn
  icases Hc with (%H0 | ⟨%t, %n, %G, #Hq, %Hcn⟩)
  · iexists fp2
    isplitr
    · ipureintro
      refine ⟨Hf2, Hw2, fun j Hj => ?_⟩
      have Hj0 : j = base0.index' := uint_Z_inj.mp (by rw [base0_index]; have := uint_Z_nonneg j; omega)
      rw [Hj0, plogTermAt_base, plogTermAt_base]
    · iexact HrF2
  obtain ⟨Hcn, Htt, HG⟩ := Hcn
  icases cq_full γ t n G $$ Hq with ⟨%HwG, #HrG⟩
  icases cq_lead γ t n G $$ Hq with ⟨%HGn, #HGl⟩
  ihave %HF2n : ⌜plogTermAt base0 (fp2 ++ ps2.log) n = some t⌝ $$ [Htbl HS]
  · by_cases Hne : t = ps2.term
    · subst Hne
      icases node_within γ id2 ps2 G Hr2 $$ HS HGl with %Hin
      have HnG := (plogTermAt_some_range _ _ _ _ HGn).2
      have HL := full_last_index _ _ ps2.log Hf2
      icases leadFull_agree γ ps2.term G (fp2 ++ ps2.log) n (by rw [HGn]; rfl)
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg n, by omega⟩)
        $$ HGl Hfl2 with %Heq
      ipureintro; rw [← Heq]; exact HGn
    · icases isCamp_ok γ id2 ps2.term F0 $$ Hc0 with %Hcok
      have Hne' : uint.Z t ≠ uint.Z ps2.term := fun h => Hne (uint_Z_inj.mp h)
      have Hcl := camp_last _ _ Hcok
      iapply lc_core γ ((uint.Z ps2.term).toNat + 1) ps2.term t n G id2 F0 (fp2 ++ ps2.log)
        (by omega) (by omega) HwF2
        (by rw [plogTermAt_prefix _ F0 _ _ Hpre (by rw [Hcl]; rfl)]; exact Hcl)
        $$ Htbl Hq Hl2 Hc0 HrF2
  have HsG : (plogTermAt base0 G c).isSome := full_term_at_some _ _ n (by rw [HGn]; rfl) Hcn
  icases full_match γ G Fn c HwG HwFn HsG HG $$ HrG HrFn with %Hm1
  icases full_match γ G (fp2 ++ ps2.log) n HwG HwF2 (by rw [HGn]; rfl) (by rw [HGn, HF2n])
    $$ HrG HrF2 with %Hm2
  iexists fp2
  isplitr
  · ipureintro
    refine ⟨Hf2, Hw2, fun j Hj => ?_⟩
    rw [← Hm1 j Hj, Hm2 j (by omega)]
  · iexact HrF2

/-- A node's full log, its commit fact and its records. -/
theorem node_full (γ : RaftNames) (id : w64) (ps : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗
      ∃ fp, ⌜FullOk ps.base fp ∧ PlogWf ps.base ps.log ∧ LogOk ps⌝ ∗
        logRecs γ base0 (fp ++ ps.log) ∗
        commitIn γ (fp ++ ps.log) ps.commit ps.term := by
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexists fp
  isplitr; · ipureintro; exact ⟨Hfull.1, Hfull.2.1, Hlog_ok⟩
  isplitr
  · iapply logRecs_full γ ps.base fp ps.log Hfull.1 $$ Hfrecs Hrecs
  · iexact Hcommit

/-- Entries of two full logs with records, at an index above both bases, that have the
same term there, are the same entry. -/
theorem full_entry_eq (γ : RaftNames) (b1 : entryID) (fp1 es1 : List raftpb.Entry)
    (b2 : entryID) (fp2 es2 : List raftpb.Entry) (i : w64) :
    FullOk b1 fp1 → FullOk b2 fp2 → PlogWf b1 es1 → PlogWf b2 es2 →
    uint.Z b1.index' < uint.Z i → uint.Z b2.index' < uint.Z i →
    (plogTermAt base0 (fp1 ++ es1) i).isSome →
    plogTermAt base0 (fp1 ++ es1) i = plogTermAt base0 (fp2 ++ es2) i →
    ⊢ logRecs (GF := GF) γ base0 (fp1 ++ es1) -∗ logRecs γ base0 (fp2 ++ es2) -∗
      ⌜plogEntryAt b1 es1 i = plogEntryAt b2 es2 i⌝ := by
  intro Hf1 Hf2 Hw1 Hw2 Hb1 Hb2 Hs Heq
  iintro #H1 #H2
  icases logRecs_agree γ _ _ _ _ $$ H1 H2 with %HRA
  ipureintro
  rw [full_term_at b1 fp1 es1 i Hf1 (by omega)] at Hs Heq
  rw [full_term_at b2 fp2 es2 i Hf2 (by omega)] at Heq
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  have := uint_Z_lt i
  obtain ⟨e1, He1, Hi1, Ht1⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ Hw1) Hx Hb1
  rw [Heq] at Hx
  obtain ⟨e2, He2, Hi2, Ht2⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ Hw2) Hx Hb2
  rw [plogEntryAt_lookup _ _ _ Hb1, plogEntryAt_lookup _ _ _ Hb2, He1, He2]
  have Hl1 := Hf1.1
  have Hl2 := Hf2.1
  have He1' : (fp1 ++ es1)[fp1.length + (uint.Z i - uint.Z b1.index' - 1).toNat]? = some e1 := by
    rw [List.getElem?_append_right (by omega)]; simpa using He1
  have He2' : (fp2 ++ es2)[fp2.length + (uint.Z i - uint.Z b2.index' - 1).toNat]? = some e2 := by
    rw [List.getElem?_append_right (by omega)]; simpa using He2
  obtain ⟨rfl, -⟩ := HRA _ _ _ _ He1' He2' (by rw [base0_index]; omega)
    (by rw [base0_index]; omega) (by rw [Ht1, Ht2]) (by rw [Hi1, Hi2])
  rfl

/-- An entry of the stored log is a term of the full log there. -/
theorem entry_term (b : entryID) (fp es : List raftpb.Entry) (i : w64) :
    FullOk b fp → uint.Z b.index' < uint.Z i ∧ uint.Z i ≤ plogLastIndexZ b es →
    (plogTermAt base0 (fp ++ es) i).isSome := by
  intro Hf Hi
  rw [full_term_at b fp es i Hf (by omega)]
  exact plogTermAt_in_range _ _ _ ⟨by omega, Hi.2⟩

theorem leader_completeness_tbl (γ : RaftNames) (id1 : w64) (ps1 : PState) (id2 : w64)
    (ps2 : PState) (i : w64) (e : raftpb.Entry) :
    uint.Z i ≤ uint.Z ps1.commit →
    plogEntryAt ps1.base ps1.log i = some e →
    ps2.role = .leader →
    uint.Z ps1.term ≤ uint.Z ps2.term →
    uint.Z ps2.base.index' < uint.Z i →
    ⊢ votesTbl (GF := GF) γ -∗ ownRaftGhost γ id1 ps1 -∗ ownRaftGhost γ id2 ps2 -∗
      ⌜plogEntryAt ps2.base ps2.log i = some e⌝ := by
  intro Hic He Hr2 Hterm Hb2
  iintro Htbl H1 H2
  icases node_full γ id1 ps1 $$ H1 with ⟨%fp1, %Hp1, #Hr1, #Hc1⟩
  obtain ⟨Hf1, Hw1, Hok1⟩ := Hp1
  icases commitIn_leader γ (fp1 ++ ps1.log) ps1.commit ps1.term id2 ps2 Hr2 Hterm
    (full_wf _ _ _ Hf1 Hw1) $$ Htbl H2 Hc1 Hr1 with ⟨%fp2, %Hp2, #Hr2'⟩
  obtain ⟨Hf2, Hw2, Hagree⟩ := Hp2
  have Hb1 : uint.Z ps1.base.index' < uint.Z i := by
    unfold plogEntryAt at He
    split at He
    · cases He
    · omega
  obtain ⟨-, -, Hcl1⟩ := Hok1
  icases full_entry_eq γ ps1.base fp1 ps1.log ps2.base fp2 ps2.log i Hf1 Hf2 Hw1 Hw2 Hb1 Hb2
    (entry_term _ _ _ _ Hf1 ⟨Hb1, by omega⟩) (Hagree i Hic) $$ Hr1 Hr2' with %Heq
  ipureintro; rw [← Heq]; exact He

/-- **Leader Completeness**: an entry a node has committed, at a term no later than a
leader's, is in the leader's log (above its compaction boundary; below it the leader's
snapshot covers it). `Qed` since 2026-10-03, from `lc_core`; over two nodes since
2026-10-05. -/
theorem leader_completeness (γ : RaftNames) (E : CoPset) (id1 : w64) (ps1 : PState)
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
  intro HE Hic He Hr2 Hterm Hb2
  iintro H1 H2
  ihave #Hinv := ownRaftGhost_inv γ id1 ps1 $$ H1
  unfold raftCommitInv
  iinv Hinv with ⟨%P, %R, HP, Hj, >Htbl, Hrest⟩ Hclose
  ihave #Hlc := leader_completeness_tbl γ id1 ps1 id2 ps2 i e Hic He Hr2 Hterm Hb2 $$ Htbl H1 H2
  imod Hclose $$ [HP Hj Htbl Hrest] with -
  · inext
    iexists P, R
    iframe
  imodintro
  iframe H1 H2 Hlc

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
theorem ownRaftGhost_term_fresh (γ : RaftNames) (id : w64) (s : PState)
    (e : raftpb.Entry) :
    s.role = .leader →
    plogLastIndexZ s.base s.log < uint.Z e.Index' →
    e.Term' = s.term →
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ isEntry γ e -∗ False := by
  intro Hr Hi Ht
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γv, %voted, %kl, H⟩ #He
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  have Hw : leaderWit (GF := GF) γ id s = isLeader γ id s.term := by
    unfold leaderWit; rw [Hr]
  rw [Hw]
  unfold leadLogOwn
  rw [Hr]
  icases Htlog with ⟨%γt, %M, %l0, %Hγt, Ha, -, %Hdom, -⟩
  unfold isEntry isEntryR isTermLog
  icases He with ⟨%pt, %ldr, %γt', %b, %l0', %F0, #Hl', ⟨%γm', %Hγm', #Htf⟩, -, #Hfr, -⟩
  rw [Ht]
  icases isLeader_unique γ id ldr s.term $$ Hlead Hl' with %Hid
  subst Hid
  rw [Htname] at Hγm'
  cases Hγm'
  icases ghost_map_lookup $$ Hterms Htf with %Hlook
  rw [Hγt] at Hlook
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (γt = γt' ∧ s.base = b) ∧ l0 = l0' := by simpa using Hlook
  icases ghost_map_lookup $$ Ha Hfr with %HM
  have := Hdom _ (by rw [HM]; rfl)
  exact (by omega : False).elim

/-- The new entries' records, named: its persistence is one instance (the instance
search on the unfolded big separating conjunction over `stampAt` took minutes). -/
def entsRec (γ : RaftNames) (t : w64) (idx : Nat → w64) (ents : List raftpb.Entry) :
    IProp GF :=
  iprop([∗list] k ↦ e ∈ ents, isEntry γ (stampAt e t (idx k)))

instance entsRec_persistent (γ : RaftNames) (t : w64) (idx : Nat → w64)
    (ents : List raftpb.Entry) : Persistent (entsRec (GF := GF) γ t idx ents) := by
  unfold entsRec; infer_instance

theorem register_props (γ : RaftNames) (t : w64) (idx : Nat → w64)
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
  induction ents generalizing idx Qs R with
  | nil =>
    intro Hlen _ _ _ _
    iintro Hra #Hidx Hs - -
    cases Qs with
    | cons _ _ => cases Hlen
    | nil =>
      imodintro
      iexists R
      iframe Hra Hidx Hs
      iapply (BigSepL.bigSepL_nil (Φ := fun k Q => iprop(∃ γp, isProp (GF := GF) γ t (idx k) γp Q ∗ propTok γp))).2
      iempintro
  | cons e ents IH =>
    intro Hlen Hfr Hinj Hpos Hnc
    cases Qs with
    | nil => cases Hlen
    | cons Q Qs =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at Hlen
    iintro Hra #Hidx Hs #Hents Haus
    icases Haus with ⟨Hau, Haus⟩
    unfold entsRec
    icases (BigSepL.bigSepL_cons (Φ := fun k e => isEntry (GF := GF) γ (stampAt e t (idx k)))).1
      $$ Hents with ⟨#Hent, #Hents'⟩
    ihave #Hents'' : entsRec γ t (fun k => idx (k + 1)) ents $$ []
    · unfold entsRec; iexact Hents'
    imod saved_pred_alloc (fun ti : w64 × w64 => Q ti.1 ti.2) DFrac.discard trivial
      with ⟨%γq, #Hsp⟩
    imod token_alloc with ⟨%γk, Htok⟩
    have Hfr0 : R !! (t, idx 0) = none := Hfr 0 (by simp)
    imod ghost_map_insert_persist (t, idx 0) (((γq, γk), e) : PropRec) Hfr0 $$ Hra
      with ⟨Hra, #Hfrag⟩
    imod IH (fun k => idx (k + 1)) Qs (<[(t, idx 0) := (((γq, γk), e) : PropRec)]> R) Hlen
        (fun k Hk => by
          rw [GMap.lookup_insert_ne]
          · exact Hfr (k + 1) (by simp; omega)
          · intro Heq
            have := Hinj 0 (k + 1) (by simp) (by simp; omega) (Prod.mk.inj Heq).2
            omega)
        (fun k1 k2 Hk1 Hk2 Heq => by
          have := Hinj (k1 + 1) (k2 + 1) (by simp; omega) (by simp; omega) Heq
          omega)
        (fun k Hk => Hpos _ (by simp; omega))
        (fun k e' Hk => Hnc _ e' (by simp; omega))
        $$ Hra [] [Hs Hau] Hents'' Haus with ⟨%R', Hra, #Hidx', Hs, Hout⟩
    · unfold propsIdx
      iapply (BigSepM.bigSepM_insert (Φ := fun (k : w64 × w64) (v : PropRec) => iprop(isEntry (GF := GF) γ (stampAt v.2 k.1 k.2) ∗
        ⌜0 < uint.Z k.2⌝)) Hfr0).2
      isplitr
      · isplitr
        · iexact Hent
        · ipureintro; exact Hpos 0 (by simp)
      · iexact Hidx
    · iapply (BigSepM.bigSepM_insert (Φ := fun (k : w64 × w64) (v : PropRec) => iprop(▷ propSlot (GF := GF) γ k v l)) Hfr0).2
      isplitl [Hau]
      · inext
        unfold propSlot
        iexists (fun ti : w64 × w64 => Q ti.1 ti.2)
        isplitr
        · iexact Hsp
        · ileft
          isplitr
          · ipureintro; exact fun e' He' => Hnc 0 e' (by simp) He'
          · iexact Hau
      · iexact Hs
    imodintro
    iexists R'
    iframe Hra Hidx' Hs
    iapply (BigSepL.bigSepL_cons (Φ := fun k Q =>
      iprop(∃ γp, isProp (GF := GF) γ t (idx k) γp Q ∗ propTok γp))).2
    isplitl [Htok]
    · iexists (γq, γk)
      unfold isProp propTok
      isplitr
      · iexists e
        isplitr
        · iexact Hfrag
        · iexact Hsp
      · iexact Htok
    · iexact Hout

private theorem logRecs_entry (γ : RaftNames) (b : entryID) (L : List raftpb.Entry)
    (j : Nat) (x : raftpb.Entry) :
    L[j]? = some x → uint.Z b.index' + (j : Int) + 1 < 2 ^ 64 →
    ⊢ logRecs (GF := GF) γ b L -∗ isEntry γ x := by
  intro Hj Hb
  have Hl : logRecs (GF := GF) γ b L ⊢ (if uint.Z b.index' + (j : Int) + 1 < 2 ^ 64
      then iprop(∃ pt, ⌜plogTermAt b L (pidx b j) = some pt⌝ ∗ isEntryR γ x pt)
      else iprop(True)) :=
    @BigSepL.bigSepL_lookup _ _ _ (fun k e => if uint.Z b.index' + (k : Int) + 1 < 2 ^ 64
      then iprop(∃ pt, ⌜plogTermAt b L (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ e pt)
      else iprop(True)) L j x Hj (Iris.Std.TCOr.l (t := fun _ _ => BIAffine.affine _))
  rw [ite_eq_left Hb] at Hl
  iintro #Hr
  icases Hl $$ Hr with ⟨%pt, -, #He⟩
  unfold isEntry
  iexists pt
  iexact He

/-- The records of the log after `Step.propose` give the new entries' records. -/
private theorem entsRec_of_logRecs (γ : RaftNames) (s : PState)
    (ents : List raftpb.Entry) :
    plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
    ⊢ logRecs (GF := GF) γ s.base (s.log ++ ents.mapIdx (stamp s.term (plastIndex s))) -∗
      entsRec γ s.term (fun k => plastIndex s + W64 1 + W64 k) ents := by
  intro Hnw
  iintro #Hr
  unfold entsRec
  iapply BigSepL.bigSepL_intro (P := iprop(□ logRecs (GF := GF) γ s.base
    (s.log ++ ents.mapIdx (stamp s.term (plastIndex s)))))
  · intro k e0 Hk
    have Hklt := (List.getElem?_eq_some_iff.mp Hk).1
    have Hk' : (s.log ++ ents.mapIdx (stamp s.term (plastIndex s)))[s.log.length + k]? =
        some (stamp s.term (plastIndex s) k e0) := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_mapIdx, Hk]
      rfl
    unfold plogLastIndexZ at Hnw
    iintro #Hr
    rw [show stampAt e0 s.term ((fun k : Nat => plastIndex s + W64 1 + W64 k) k)
        = stamp s.term (plastIndex s) k e0 from rfl]
    iapply logRecs_entry γ s.base _ _ _ Hk' (by push_cast; omega) $$ Hr
  · iexact Hr

/-- (Not in `GhostState.lean`, which declares only its timelessness.) -/
private instance committedJust_persistent' (γ : RaftNames) (l : List raftpb.Entry) :
    Persistent (committedJust (GF := GF) γ l) := by
  unfold committedJust; infer_instance

/-- `Step.propose`, registering the proposals: each update `propAu γ e Q` is registered
at the `(term, index)` its entry is stamped with, and the client gets `isProp` and the
token for it. (Rocq's `let s' := pappend s (imap …) in` is inlined.) -/
theorem ownRaftGhost_step_propose_reg (γ : RaftNames) (id : w64) (s : PState)
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
  intro Hrole Hnw Hlen
  iintro Hown Haus
  ihave #Hinv := ownRaftGhost_inv γ id s $$ Hown
  unfold raftCommitInv
  -- hidden from `iinv`'s side-condition solver, which loops on it
  have Hnw' : PLift (plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64) := ⟨Hnw⟩
  clear Hnw
  iinv Hinv with ⟨%P, %R, >HP, >#Hj, >Htbl, >Hra, >#Hidxm, Hslots⟩ Hclose
  have Hnw := Hnw'.down
  have HL0 := plogLastIndexZ_nonneg s.base s.log
  have Hidx : ∀ k, k < ents.length →
      uint.Z (plastIndex s + W64 1 + W64 (k : Int)) = plogLastIndexZ s.base s.log + 1 + k := by
    intro k Hk; exact stamp_index_eq _ k HL0 (by omega)
  icases (BigSepM.bigSepM_later).1 $$ Hslots with Hslots
  -- the new keys are fresh in the registry
  ihave %Hfr : ⌜∀ k, k < ents.length →
      R !! (s.term, plastIndex s + W64 1 + W64 (k : Int)) = none⌝ $$ [Hown]
  · iintro %k %Hk
    cases Hv : R !! (s.term, plastIndex s + W64 1 + W64 (k : Int)) with
    | none => ipureintro; rfl
    | some v =>
      unfold propsIdx
      ihave ⟨#Hie, -⟩ := BigSepM.bigSepM_lookup (Φ := fun (k : w64 × w64) (v : PropRec) =>
        iprop(isEntry (GF := GF) γ (stampAt v.2 k.1 k.2) ∗ ⌜0 < uint.Z k.2⌝)) Hv $$ Hidxm
      ihave Hf := ownRaftGhost_term_fresh γ id s _ Hrole
        (by show _ < uint.Z (plastIndex s + W64 1 + W64 (k : Int)); rw [Hidx k Hk]; omega) rfl
        $$ Hown Hie
      iexfalso; iexact Hf
  -- the global log has no entry of the term at the new indices
  ihave %Hnc : ⌜∀ k e, k < ents.length → P[pos (plastIndex s + W64 1 + W64 (k : Int))]? = some e →
      e.Term' ≠ s.term⌝ $$ [Hown]
  · iintro %k %e %Hk %He %Het
    unfold committedJust
    icases Hj with (%H0 | ⟨%t0, %n0, %G0, #Hcq0, %HP⟩)
    · subst H0; simp at He
    subst HP
    icases cq_full γ t0 n0 G0 $$ Hcq0 with ⟨%HwG0, #HrG0⟩
    have He' := prefix_lookup_Some He (List.take_prefix _ _)
    have Hei := HwG0 _ _ He'
    rw [base0_index] at Hei
    have Hik := Hidx k Hk
    have := uint_Z_lt (plastIndex s + W64 1 + W64 (k : Int))
    unfold pos at He' Hei
    ihave #Her := logRecs_entry γ base0 G0 _ e He' (by rw [base0_index]; omega) $$ HrG0
    iapply ownRaftGhost_term_fresh γ id s e Hrole (by omega) Het $$ Hown Her
  -- the step
  imod ownRaftGhost_step_propose γ id s ents Hrole Hnw $$ Hown with Hown
  ihave #⟨-, #Hrecs'⟩ := ownRaftGhost_log γ id _ $$ Hown
  rw [psendMsgs_base, psendMsgs_log,
    show (pappend s (ents.mapIdx (stamp s.term (plastIndex s)))).base = s.base from rfl,
    show (pappend s (ents.mapIdx (stamp s.term (plastIndex s)))).log
      = s.log ++ ents.mapIdx (stamp s.term (plastIndex s)) from rfl]
  ihave #Hents := entsRec_of_logRecs γ s ents Hnw $$ Hrecs'
  imod register_props γ s.term (fun k => plastIndex s + W64 1 + W64 (k : Int)) P ents Qs R Hlen
      Hfr
      (fun k1 k2 Hk1 Hk2 Heq => by
        have Hz : uint.Z (plastIndex s + W64 1 + W64 (k1 : Int))
            = uint.Z (plastIndex s + W64 1 + W64 (k2 : Int)) := by rw [Heq]
        rw [Hidx k1 Hk1, Hidx k2 Hk2] at Hz
        omega)
      (fun k Hk => by rw [Hidx k Hk]; omega)
      Hnc
      $$ Hra Hidxm Hslots Hents Haus with ⟨%R', Hra, #Hidx', Hslots, Hout⟩
  icases (BigSepM.bigSepM_later).2 $$ Hslots with Hslots
  imod Hclose $$ [HP Htbl Hra Hslots] with -
  · inext
    iexists P, R'
    iframe HP Hj Htbl Hra Hidx' Hslots
  imodintro
  isplitl [Hown]
  · iexact Hown
  · iexact Hout

/-- Collecting: once the client's entry is committed -- a committed log has an entry of
term `t` at `i` -- the token buys the result, under two laters (the invariant it was
stored in; the saved predicate). -/
theorem prop_collect (γ : RaftNames) (E : CoPset) (t i : w64) (γp : GName × GName)
    (Q : w64 → w64 → IProp GF) (l : List raftpb.Entry) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv γ -∗ isProp γ t i γp Q -∗ propTok γp -∗ isCommitted γ l -∗
      ⌜∃ e, l[pos i]? = some e ∧ e.Term' = t⌝ ={E}=∗ ▷ ▷ Q t i := by
  intro HE
  unfold isProp
  iintro #Hinv ⟨%e0, #Hfrag, #Hsp⟩ Htok #Hc %Hl
  unfold raftCommitInv
  iinv Hinv with ⟨%P, %R, >HP, >#Hj, >Htbl, >Hra, >#Hidx, Hslots⟩ Hclose
  icases ghost_map_lookup $$ Hra Hfrag with %Hv
  icases isCommitted_prefix γ l P $$ Hc HP with %Hpre
  obtain ⟨e, He, Het⟩ := Hl
  have HeP := prefix_lookup_Some He Hpre
  icases (BigSepM.bigSepM_later).1 $$ Hslots with Hslots
  icases (BigSepM.bigSepM_insert_acc (Φ := fun (k : w64 × w64) (v : PropRec) =>
    iprop(▷ propSlot (GF := GF) γ k v P)) Hv) $$ Hslots with ⟨Hs, Hclose'⟩
  unfold propSlot
  icases Hs with ⟨%Φ, #Hsp', Hst⟩
  icases Hst with (⟨>%Hnc, -⟩ | ⟨>%Hdone, HQ⟩ | >Htok')
  · exact absurd Het (Hnc e HeP)
  · ihave #Heq : ▷ ▷ (Φ (t, i) ≡ Q t i) $$ []
    · inext
      iapply saved_pred_agree γp.1 DFrac.discard DFrac.discard Φ
        (fun ti : w64 × w64 => Q ti.1 ti.2) (t, i) $$ Hsp' Hsp
    ihave Hcl := Hclose' $$ %(((γp.1, γp.2), e0) : PropRec) [Htok]
    · inext
      iexists Φ
      isplitr
      · iexact Hsp'
      · unfold propTok
        iright; iright; iexact Htok
    rw [show Std.insert R (t, i) (((γp.1, γp.2), e0) : PropRec) = R from
      GMap.insert_id R (t, i) _ Hv]
    icases (BigSepM.bigSepM_later).2 $$ Hcl with Hcl
    imod Hclose $$ [HP Htbl Hra Hcl] with -
    · inext
      iexists P, R
      iframe HP Hj Htbl Hra Hidx Hcl
    imodintro
    inext
    inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨Hiff, -⟩
    iapply Hiff $$ HQ
  · unfold propTok
    iexfalso
    iapply token_exclusive $$ Htok Htok'

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
  induction ids using GMap.map_ind with
  | h0 =>
    imodintro
    iexists ∅
    isplitr
    · ipureintro; exact GMap.dom_empty
    · iapply (BigSepM.bigSepM_empty (Φ := fun (x : w64) (_u : Unit) =>
        iprop(∃ γx, ⌜(∅ : GMap w64 GName) !! x = some γx⌝ ∗
          ghostMapAuth (GF := GF) γx 1 (∅ : GMap K V)))).2
      iempintro
  | hins x u ids Hx IH =>
    imod IH with ⟨%names, %Hdom, Hm⟩
    imod ghost_map_alloc_empty (GF := GF) (K := K) (V := V) with ⟨%γx, Hauth⟩
    imodintro
    iexists <[x := γx]> names
    isplitr
    · ipureintro
      rw [GMap.dom_insert, Hdom, GMap.insert_union_singleton_l]
      rfl
    iapply (BigSepM.bigSepM_insert (Φ := fun (y : w64) (_u : Unit) =>
        iprop(∃ γy, ⌜(<[x := γx]> names) !! y = some γy⌝ ∗
          ghostMapAuth (GF := GF) γy 1 (∅ : GMap K V))) Hx).2
    isplitl [Hauth]
    · iexists γx
      isplitr
      · ipureintro; exact GMap.lookup_insert _ _ _
      · iexact Hauth
    ihave H := BigSepM.bigSepM_impl $$ Hm
    iapply H
    imodintro
    iintro %y %uy %Hy ⟨%γy, %Hγy, Ha⟩
    iexists γy
    isplitr
    · ipureintro
      rw [GMap.lookup_insert_ne]
      · exact Hγy
      · rintro rfl
        have Hy' : ids !! x = some uy := Hy
        rw [Hx] at Hy'; cases Hy'
    · iexact Ha

theorem alloc_evs (ids : GSet w64) :
    ⊢ |==> ∃ (names : GMap w64 GName),
        [∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜names !! x = some γx⌝ ∗
                               monoListAuthOwn (GF := GF) γx 1 ([] : List Aev) := by
  induction ids using GMap.map_ind with
  | h0 =>
    imodintro
    iexists ∅
    iapply (BigSepM.bigSepM_empty (Φ := fun (x : w64) (_u : Unit) =>
      iprop(∃ γx, ⌜(∅ : GMap w64 GName) !! x = some γx⌝ ∗
        monoListAuthOwn (GF := GF) γx 1 ([] : List Aev)))).2
    iempintro
  | hins x u ids Hx IH =>
    imod IH with ⟨%names, Hm⟩
    imod mono_list_own_alloc (GF := GF) ([] : List Aev) with ⟨%γx, Hauth, -⟩
    imodintro
    iexists <[x := γx]> names
    iapply (BigSepM.bigSepM_insert (Φ := fun (y : w64) (_u : Unit) =>
        iprop(∃ γy, ⌜(<[x := γx]> names) !! y = some γy⌝ ∗
          monoListAuthOwn (GF := GF) γy 1 ([] : List Aev))) Hx).2
    isplitl [Hauth]
    · iexists γx
      isplitr
      · ipureintro; exact GMap.lookup_insert _ _ _
      · iexact Hauth
    ihave H := BigSepM.bigSepM_impl $$ Hm
    iapply H
    imodintro
    iintro %y %uy %Hy ⟨%γy, %Hγy, Ha⟩
    iexists γy
    isplitr
    · ipureintro
      rw [GMap.lookup_insert_ne]
      · exact Hγy
      · rintro rfl
        have Hy' : ids !! x = some uy := Hy
        rw [Hx] at Hy'; cases Hy'
    · iexact Ha

/-- The log ghost state of a node in the initial state, from its fresh maps. -/
private theorem ownLogGhost_init (γ : RaftNames) (id : w64) (γm γa γc γl γw γe : GName) :
    γ.reTerms !! id = some γm → γ.reAcks !! id = some γa → γ.reCamp !! id = some γc →
    γ.reVlogs !! id = some γl → γ.reWins !! id = some γw → γ.reEvs !! id = some γe →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ [] -∗
      ghostMapAuth γm 1 (∅ : GMap w64 TermRec) -∗
      ghostMapAuth γa 1 (∅ : GMap (w64 × w64) Unit) -∗
      ghostMapAuth γc 1 (∅ : GMap w64 (List raftpb.Entry)) -∗
      ghostMapAuth γl 1 (∅ : GMap Nat ((w64 × Bool) × List raftpb.Entry)) -∗
      ghostMapAuth γw 1 (∅ : GMap w64 (GSet w64)) -∗
      monoListAuthOwn γe 1 ([] : List Aev) -∗
      ownLogGhost γ id initPState none := by
  intro Hγm Hγa Hγc Hγl Hγw Hγe
  iintro #Hinv #Hc0 Hm Ha Hc Hl Hw He
  unfold ownLogGhost
  iexists γm, ∅, γa, ∅, [], γc, ∅, γl, ∅, γw, ∅
  iframe Hm Ha Hc Hl Hw Hinv
  have Hrole : initPState.role = .follower := rfl
  isplitr; · ipureintro; exact Hγm
  isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · ipureintro; intro t Ht; simp at Ht
  isplitr; · unfold leadLogOwn; rw [Hrole]; iempintro
  isplitr; · ipureintro; exact Hγa
  isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · ipureintro; intro k Hk; simp at Hk
  isplitr; · unfold acksOk; rw [Hrole]; iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr
  · ipureintro
    refine ⟨fun k e Hk => by simp [initPState] at Hk, ?_, ?_⟩ <;>
      simp [initPState, plogLastIndexZ]
  isplitr
  · unfold logRecs
    rw [show initPState.log = ([] : List raftpb.Entry) from rfl]
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr; · unfold matchedOk; rw [Hrole]; iempintro
  isplitr; · unfold commitIn; ileft; ipureintro; rfl
  isplitr; · unfold baseOk; ileft; ipureintro; rfl
  isplitr
  · ipureintro
    refine ⟨FullOk_base0, fun k e Hk => by simp [initPState] at Hk, ?_⟩
    intro j x Hx
    rw [show ([] ++ initPState.log : List raftpb.Entry) = [] from rfl] at Hx
    have Hr := plogTermAt_some_range _ _ _ _ Hx
    unfold plogLastIndexZ at Hr
    rw [base0_index] at Hr
    have Hj : j = W64 0 := uint_Z_inj.mp (by
      have h2 := Hr.2
      simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at h2
      have h1 := uint_Z_nonneg j
      rw [show uint.Z (W64 0) = 0 from rfl]; omega)
    subst Hj
    have H0 := plogTermAt_base base0 ([] : List raftpb.Entry)
    rw [show base0.index' = W64 0 from rfl] at H0
    rw [H0] at Hx
    cases Hx
    exact ⟨Int.le_refl _, fun h => by cases h⟩
  isplitr; · unfold logRecs; iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr; · ipureintro; exact Hγc
  isplitr; · ipureintro; intro T HT; simp at HT
  isplitr; · unfold campOwn; rw [Hrole]; iempintro
  isplitr; · ipureintro; exact Hγl
  isplitr; · unfold vlogsOk; iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · unfold histsOk; iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · ipureintro; exact Hγw
  isplitr; · ipureintro; intro t Ht; simp at Ht
  isplitr; · unfold klOk; ipureintro; rw [Hrole]; intro h; cases h
  isplitl [He]
  · unfold ownEvs
    iexists γe, []
    isplitr; · ipureintro; exact Hγe
    isplitl [He]; · iexact He
    ipureintro
    refine ⟨fun p1 p2 e1 e2 _ H1 _ => by simp at H1, fun e He => by simp at He,
      fun t i Hi => by simp at Hi⟩
  · unfold cprefix
    rw [show ((([] : List raftpb.Entry) ++ initPState.log).take (uint.Z initPState.commit).toNat)
      = [] from rfl]
    iexact Hc0

private theorem ghostMapAuth_halves {K V : Type} [DecidableEq K] [Pos.Countable K]
    [Pos.Countable V] (γx : GName) (m : GMap K V) :
    ⊢ ghostMapAuth (GF := GF) γx 1 m -∗
      ghostMapAuth γx (1 : Qp).half m ∗ ghostMapAuth γx (1 : Qp).half m := by
  have h : ghostMapAuth (GF := GF) γx ((1 : Qp).half + (1 : Qp).half) m ⊣⊢
      ghostMapAuth γx (1 : Qp).half m ∗ ghostMapAuth γx (1 : Qp).half m :=
    (ghostMapAuth_fractional γx m).fractional _ _
  rw [Qp.half_add_half] at h
  iintro H
  iapply h.1 $$ H

private theorem tbl_of_ids (nv : GMap w64 GName) (P : w64 → GName → IProp GF) :
    ∀ m : GMap w64 GName, (∀ k v, m !! k = some v → nv !! k = some v) →
    ⊢ ([∗map] x ↦ _u ∈ toMap (domSet m), ∃ γx, ⌜nv !! x = some γx⌝ ∗ P x γx) -∗
      [∗map] x ↦ γx ∈ m, P x γx := by
  intro m
  induction m using GMap.map_ind with
  | h0 =>
    intro _
    rw [GMap.dom_empty]
    iintro -
    iapply (BigSepM.bigSepM_empty).2
    iempintro
  | hins k v m Hk IH =>
    intro Hsub
    have Hdk : (domSet m) !! k = none := by simp [domSet, Hk]
    rw [show domSet (<[k := v]> m) = <[k := ()]> (domSet m) from GMap.fmap_insert _ _ _ _]
    iintro H
    icases (BigSepM.bigSepM_insert Hdk).1 $$ H with ⟨⟨%γx, %Hγx, HP⟩, H⟩
    have : γx = v := by
      rw [Hsub k v (GMap.lookup_insert _ _ _)] at Hγx; cases Hγx; rfl
    subst this
    iapply (BigSepM.bigSepM_insert Hk).2
    isplitl [HP]
    · iexact HP
    · iapply IH (fun k' v' Hk' => Hsub k' v' (by
        rw [GMap.lookup_insert_ne]
        · exact Hk'
        · rintro rfl; rw [Hk] at Hk'; cases Hk')) $$ H

/-- A node's ghost state in the initial state, from its fresh resources. -/
private theorem ownRaftGhost_init (γ : RaftNames) (id : w64)
    (γv γm γa γc γl γw γe : GName) :
    id ≠ W64 0 →
    γ.reVotes !! id = some γv → γ.reTerms !! id = some γm → γ.reAcks !! id = some γa →
    γ.reCamp !! id = some γc → γ.reVlogs !! id = some γl → γ.reWins !! id = some γw →
    γ.reEvs !! id = some γe →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ [] -∗
      ghostMapAuth γv (1 : Qp).half (∅ : GMap w64 w64) -∗
      ghostMapAuth γm 1 (∅ : GMap w64 TermRec) -∗
      ghostMapAuth γa 1 (∅ : GMap (w64 × w64) Unit) -∗
      ghostMapAuth γc 1 (∅ : GMap w64 (List raftpb.Entry)) -∗
      ghostMapAuth γl 1 (∅ : GMap Nat ((w64 × Bool) × List raftpb.Entry)) -∗
      ghostMapAuth γw 1 (∅ : GMap w64 (GSet w64)) -∗
      monoListAuthOwn γe 1 ([] : List Aev) -∗
      ownRaftGhost γ id initPState := by
  intro Hnz Hγv Hγm Hγa Hγc Hγl Hγw Hγe
  iintro #Hinv #Hc0 Hv Hm Ha Hc Hl Hw He
  ihave Hlg := ownLogGhost_init γ id γm γa γc γl γw γe Hγm Hγa Hγc Hγl Hγw Hγe
    $$ Hinv Hc0 Hm Ha Hc Hl Hw He
  have Hrole : initPState.role = .follower := rfl
  unfold ownRaftGhost
  iexists γv, ∅, none
  isplitr; · ipureintro; exact Hγv
  isplitr; · ipureintro; exact Hnz
  isplitl [Hv]; · iexact Hv
  isplitr; · ipureintro; exact ⟨fun t Ht => by simp at Ht, by simp [initPState]⟩
  isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr
  · rw [show initPState.outbox = [] from rfl]
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · rw [show initPState.votes = ∅ from rfl, granted_empty]
    iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · unfold leaderWit; rw [Hrole]; iempintro
  isplitl [Hlg]; · iexact Hlg
  isplitr; · ipureintro; intro _ h; exact Hnz h.symm
  isplitr; · ipureintro; intro _; rfl
  isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
  ipureintro
  exact ⟨fun h => absurd Hrole h, fun h => by rw [Hrole] at h; cases h⟩

private theorem alloc_nodes (γ : RaftNames) (ids : GSet w64) :
    W64 0 ∉ ids →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ [] -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reVotes !! x = some γx⌝ ∗
        ghostMapAuth γx (1 : Qp).half (∅ : GMap w64 w64)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reTerms !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 TermRec)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reAcks !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap (w64 × w64) Unit)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reCamp !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 (List raftpb.Entry))) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reVlogs !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap Nat ((w64 × Bool) × List raftpb.Entry))) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reWins !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 (GSet w64))) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reEvs !! x = some γx⌝ ∗
        monoListAuthOwn γx 1 ([] : List Aev)) -∗
      [∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id initPState := by
  induction ids using GMap.map_ind with
  | h0 =>
    intro _
    iintro - - - - - - - - -
    iapply (BigSepM.bigSepM_empty).2
    iempintro
  | hins x u ids Hx IH =>
    intro Hnz
    have Hxm : x ∈ (<[x := u]> ids : GSet w64) :=
      (GMap.elem_of_gset _ _).mpr (by rw [GMap.lookup_insert])
    have Hsub : ∀ y, y ∈ ids → y ∈ (<[x := u]> ids : GSet w64) := by
      intro y Hy
      rw [GMap.elem_of_gset] at Hy ⊢
      by_cases Hxy : x = y
      · subst Hxy; rw [Hx] at Hy; cases Hy
      · rw [GMap.lookup_insert_ne _ _ Hxy]; exact Hy
    iintro #Hinv #Hc0 Hv Hm Ha Hc Hl Hw He
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hv with ⟨⟨%γv, %Hγv, Hv1⟩, Hv⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hm with ⟨⟨%γm, %Hγm, Hm1⟩, Hm⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Ha with ⟨⟨%γa, %Hγa, Ha1⟩, Ha⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hc with ⟨⟨%γc, %Hγc, Hc1⟩, Hc⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hl with ⟨⟨%γl, %Hγl, Hl1⟩, Hl⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hw with ⟨⟨%γw, %Hγw, Hw1⟩, Hw⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ He with ⟨⟨%γe, %Hγe, He1⟩, He⟩
    iapply (BigSepM.bigSepM_insert Hx).2
    isplitl [Hv1 Hm1 Ha1 Hc1 Hl1 Hw1 He1]
    · iapply ownRaftGhost_init γ x γv γm γa γc γl γw γe
        (fun h => Hnz (h ▸ Hxm)) Hγv Hγm Hγa Hγc Hγl Hγw Hγe
        $$ Hinv Hc0 Hv1 Hm1 Ha1 Hc1 Hl1 Hw1 He1
    · iapply IH (fun h => Hnz (Hsub _ h)) $$ Hinv Hc0 Hv Hm Ha Hc Hl Hw He

theorem ownRaftGhost_alloc (E : CoPset) (cfg ids : GSet w64) :
    W64 0 ∉ ids →
    ⊢ |={E}=> ∃ γ : RaftNames, ⌜γ.reCfg = cfg⌝ ∗ raftCommitInv (GF := GF) γ ∗
        isCommitted γ [] ∗
        [∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id initPState := by
  intro Hnz
  imod alloc_maps (GF := GF) (K := w64) (V := w64) ids with ⟨%nv, %Hnv, Hv⟩
  imod alloc_maps (GF := GF) (K := w64) (V := TermRec) ids with ⟨%nt, -, Ht⟩
  imod alloc_maps (GF := GF) (K := w64 × w64) (V := Unit) ids with ⟨%na, -, Ha⟩
  imod alloc_maps (GF := GF) (K := w64) (V := List raftpb.Entry) ids with ⟨%nc, -, Hc⟩
  imod alloc_maps (GF := GF) (K := Nat) (V := (w64 × Bool) × List raftpb.Entry) ids
    with ⟨%nl, -, Hl⟩
  imod alloc_maps (GF := GF) (K := w64) (V := GSet w64) ids with ⟨%nw, -, Hw⟩
  imod alloc_evs (GF := GF) ids with ⟨%ne, He⟩
  imod ownCommitted_alloc (GF := GF) with ⟨%γc, Hcauth, #Hclb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := PropRec) with ⟨%γpr, Hpra⟩
  obtain ⟨γ0, Hγ0⟩ : ∃ γ0 : RaftNames,
      γ0 = ⟨cfg, nv, nt, na, nc, nl, nw, ne, γc, γpr⟩ := ⟨_, rfl⟩
  have e1 : γ0.reVotes = nv := by rw [Hγ0]
  have e2 : γ0.reTerms = nt := by rw [Hγ0]
  have e3 : γ0.reAcks = na := by rw [Hγ0]
  have e4 : γ0.reCamp = nc := by rw [Hγ0]
  have e5 : γ0.reVlogs = nl := by rw [Hγ0]
  have e6 : γ0.reWins = nw := by rw [Hγ0]
  have e7 : γ0.reEvs = ne := by rw [Hγ0]
  have e8 : γ0.reCommit = γc := by rw [Hγ0]
  have e9 : γ0.reProps = γpr := by rw [Hγ0]
  have e0 : γ0.reCfg = cfg := by rw [Hγ0]
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9]
  -- each vote map: half to the node, half to the table
  ihave Hv2 : ([∗map] x ↦ _u ∈ toMap ids,
      iprop((∃ γx, ⌜γ0.reVotes !! x = some γx⌝ ∗
          ghostMapAuth (GF := GF) γx (1 : Qp).half (∅ : GMap w64 w64)) ∗
        (∃ γx, ⌜γ0.reVotes !! x = some γx⌝ ∗
          ghostMapAuth (GF := GF) γx (1 : Qp).half (∅ : GMap w64 w64)))) $$ [Hv]
  · iapply BigSepM.bigSepM_impl $$ Hv
    imodintro
    iintro %x %u %_ ⟨%γx, %Hx, Hax⟩
    icases ghostMapAuth_halves γx _ $$ Hax with ⟨Ha1, Ha2⟩
    isplitl [Ha1]
    · iexists γx
      isplitr
      · ipureintro; exact Hx
      · iexact Ha1
    · iexists γx
      isplitr
      · ipureintro; exact Hx
      · iexact Ha2
  rw [BigSepM.bigSepM_sep_eq]
  icases Hv2 with ⟨Hv, Hvt⟩
  ihave Htbl : votesTbl (GF := GF) γ0 $$ [Hvt]
  · unfold votesTbl
    rw [← Hnv, e1]
    ihave Ht' := tbl_of_ids nv
      (fun _ γv => ghostMapAuth (GF := GF) γv (1 : Qp).half (∅ : GMap w64 w64))
      nv (fun _ _ h => h) $$ Hvt
    iapply BigSepM.bigSepM_impl $$ Ht'
    imodintro
    iintro %v %γv %_ Hav
    iexists ∅
    isplitl [Hav]
    · iexact Hav
    · iapply (BigSepM.bigSepM_empty).2; iempintro
  imod inv_alloc raftN E iprop(∃ l, ∃ (R : GMap (w64 × w64) PropRec),
               ownCommitted γ0 l ∗ committedJust γ0 l ∗ votesTbl γ0 ∗
               ghostMapAuth γ0.reProps 1 R ∗ propsIdx γ0 R ∗
               [∗map] k ↦ v ∈ R, propSlot γ0 k v l) $$ [Hcauth Htbl Hpra] with #Hinv
  · inext
    iexists [], ∅
    isplitl [Hcauth]
    · rw [ownCommitted_unseal]; unfold ownCommittedDef; iexact Hcauth
    isplitr
    · unfold committedJust; ileft; ipureintro; rfl
    isplitl [Htbl]; · iexact Htbl
    isplitl [Hpra]; · iexact Hpra
    isplitr
    · unfold propsIdx; iapply (BigSepM.bigSepM_empty).2; iempintro
    · iapply (BigSepM.bigSepM_empty).2; iempintro
  ihave #Hinv' : raftCommitInv (GF := GF) γ0 $$ []
  · unfold raftCommitInv; iexact Hinv
  ihave #Hc0 : isCommitted (GF := GF) γ0 [] $$ []
  · rw [isCommitted_unseal]; unfold isCommittedDef; iexact Hclb
  imodintro
  iexists γ0
  isplitr; · ipureintro; exact e0
  isplitr; · iexact Hinv'
  isplitr; · iexact Hc0
  iapply alloc_nodes γ0 ids Hnz $$ Hinv' Hc0 Hv Ht Ha Hc Hl Hw He

end ghost

/-! ## Derived conveniences used by `Link.lean` -/

section lemmas
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- Taking a step that consumes a single known message. -/
theorem ownRaftGhost_step_1 (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
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
theorem ownRaftGhost_step_0 (γ : RaftNames) (id : w64) (s s' : PState) :
    Step γ.reCfg id s [] s' →
    ⊢ ownRaftGhost (GF := GF) γ id s ={⊤}=∗ ownRaftGhost γ id s' := by
  intro Hstep
  iintro Hown
  iapply ownRaftGhost_step γ id s [] s' Hstep $$ [] Hown
  iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  iempintro

end lemmas

/-! ### The commit index never moves back (2026-10-09)

Every rule of `Step` keeps `commit` or raises it: `plogCommitTo` (`appAccept`,
`heartbeat`) takes the maximum, `commit`/`snapRestore`/`snapFastfwd` have
`commit < n` as a premise, and every other rule leaves it alone. `RawNode.Advance` needs
it to carry a queued `MsgStorageApplyResp`'s "its entries are committed" across the
steps before it. (Until 2026-10-09 `PstepCommitMono`, a premise of `Advance`'s spec.) -/

theorem plogCommitTo_ge [FfiSyntax] (c t : w64) : uint.Z c ≤ uint.Z (plogCommitTo c t) := by
  unfold plogCommitTo; split <;> omega

theorem Step.commit_mono [FfiSyntax] {cfg : GSet w64} {id : w64} {ps : PState}
    {recv : List Msg} {ps' : PState} (H : Step cfg id ps recv ps') :
    uint.Z ps.commit ≤ uint.Z ps'.commit := by
  induction H with
  | refl => exact Int.le_refl _
  | trans _ _ _ _ _ _ _ ih1 ih2 => omega
  | appAccept => exact plogCommitTo_ge _ _
  | heartbeat => exact plogCommitTo_ge _ _
  | commit _ _ _ h => exact Int.le_of_lt h
  | snapRestore _ _ _ _ _ _ _ _ _ h => simp only [psendMsgs]; omega
  | snapFastfwd _ _ _ _ _ _ _ _ _ h => simp only [psendMsgs]; omega
  | _ => simp [psendMsgs, pbecomeFollower, pbecomeCandidate, pwinState, pappend, pbecomeLeader,
      padoptLeader]

end EtcdGrove
end Perennial
