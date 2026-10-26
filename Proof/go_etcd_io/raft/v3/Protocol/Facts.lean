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
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

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
theorem heartbeat_commit_le_last (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) {md : Bool} :
    m.ty = .heartbeat →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    (m.term = ps.term → ps.role ≠ .leader) →
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ isMessage γ m -∗
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
theorem app_recv_wf (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) {md : Bool} :
    m.ty = .app →
    m.dst = id →
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ isMessage γ m -∗
      ⌜PlogWf (entryID.mk m.logterm m.index) m.entries ∧
        uint.Z m.index + (m.entries.length : Int) + 1 < 2 ^ 64⌝ := by
  intro Hty _
  simp only [isMessage, Hty]
  iintro - ⟨%Hpay, -⟩
  ipureintro; exact Hpay

/-- `maybeAppend` panics if the first conflicting index is at or below the commit index
(`ci ≤ l.committed`). Under `maybeAppend`'s caller's premise `committed ≤ m.Index` that is
arithmetic: a conflict is the index of one of the batch's entries, which are at
`m.Index + 1` and above (`AppPayloadOk`). (Until 2026-10-02 this was admitted as a
consequence of Leader Completeness; the premise makes it local. The term premise is not
needed.) -/
theorem app_no_conflict_below_commit (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) {md : Bool} :
    m.ty = .app →
    m.dst = id →
    uint.Z ps.term ≤ uint.Z m.term →
    uint.Z ps.commit ≤ uint.Z m.index →
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ isMessage γ m -∗
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
  obtain ⟨Hwf, -⟩ := Hpay
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

theorem ownRaftGhost_committed (γ : RaftNames) (id : w64) (s : PState) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
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

/-! ### Leader Completeness (2026-10-03; over two nodes since 2026-10-05)

An entry a node has committed, at a term no later than a leader's, is in the leader's
log. The pivot argument (`lc_core`) needs the vote table, which is in the invariant: the
statement is a fancy update. (Until 2026-10-05 it was stated over the whole cluster,
`cluster_ghost`, because the pivot voter's records were in its own ghost state.) -/

/-! ### Fresh terms at a leader (2026-10-05)

A leader of `t` has nothing in its term log past its last index
(`ownRaftGhost_term_fresh`), and a leader's term is nonzero. (Until 2026-10-10 the
proposal registry was keyed by `(term, index)` and registered at `Step.propose`, which
used the first; it is now keyed by data and filled before the proposal leaves its node:
"Depositing and collecting proposals" below.) -/

/-! ### Depositing and collecting proposals (2026-10-10)

`prop_deposit` puts a client's atomic update (with a later credit) in the registry,
keyed by its data, which must be fresh (`propFresh`); `commit_extend` fires it
(`LeaderCompleteness.lean`). `prop_collect` trades the client's ticket for the result,
given the first committed entry with that data. `committed_data` gives the data of a
committed log's entries. -/

/-- Two lists of data for the same entries are the same. -/
theorem entDataIs_list_agree (γ : RaftNames) (l : List EntryM) :
    ∀ (o1 o2 : List (Option (List w8))),
    ⊢ ([∗list] e;o ∈ l;o1, entDataIs (GF := GF) γ e o) -∗
      ([∗list] e;o ∈ l;o2, entDataIs γ e o) -∗ ⌜o1 = o2⌝ := by
  induction l with
  | nil =>
    intro o1 o2
    iintro H1 H2
    ihave %h1 := BigSepL2.bigSepL2_length $$ H1
    ihave %h2 := BigSepL2.bigSepL2_length $$ H2
    ipureintro
    simp only [List.length_nil] at h1 h2
    rw [List.length_eq_zero_iff.mp h1.symm, List.length_eq_zero_iff.mp h2.symm]
  | cons e l ih =>
    intro o1 o2
    cases o1 with
    | nil =>
      iintro H1 _
      ihave %h := BigSepL2.bigSepL2_length $$ H1
      simp at h
    | cons x1 xs1 =>
    cases o2 with
    | nil =>
      iintro _ H2
      ihave %h := BigSepL2.bigSepL2_length $$ H2
      simp at h
    | cons x2 xs2 =>
    iintro H1 H2
    icases (BigSepL2.bigSepL2_cons).1 $$ H1 with ⟨Hx1, H1⟩
    icases (BigSepL2.bigSepL2_cons).1 $$ H2 with ⟨Hx2, H2⟩
    ihave %h := entDataIs_agree γ e x1 x2 $$ Hx1 Hx2
    ihave %h' := ih xs1 xs2 $$ H1 H2
    ipureintro
    rw [h, h']

/-- The data of a prefix of the entries is a prefix of their data. -/
theorem entDataIs_list_prefix (γ : RaftNames) (l P : List EntryM)
    (o oP : List (Option (List w8))) (Hp : l <+: P) :
    ⊢ ([∗list] e;o ∈ l;o, entDataIs (GF := GF) γ e o) -∗
      ([∗list] e;o ∈ P;oP, entDataIs γ e o) -∗ ⌜o <+: oP⌝ := by
  obtain ⟨r, rfl⟩ := Hp
  iintro #H1 #H2
  icases (BigSepL2.bigSepL2_app_inv_left (Φ := fun _ e o => entDataIs (GF := GF) γ e o)) $$ H2
    with ⟨%o1, %o2, %Ho, #H2, -⟩
  ihave %Heq := entDataIs_list_agree γ l o o1 $$ H1 H2
  ipureintro
  rw [Ho, Heq]
  exact List.prefix_append _ _

/-- No committed entry holds a data the registry does not have: every committed client entry
was deposited. -/
theorem ods_not_fresh (γ : RaftNames) (l : List EntryM) (ods : List (Option (List w8)))
    (R : GMap (List w8) PropRec) (d : List w8) (HRd : R !! d = none) :
    ⊢ ([∗list] e;o ∈ l;ods, entDataIs (GF := GF) γ e o) -∗ ghostMapAuth γ.reProps 1 R -∗
      ⌜some d ∉ ods⌝ := by
  iintro #H Hra %Hin
  obtain ⟨j, Hj⟩ := List.mem_iff_getElem?.mp Hin
  ihave %Hlen := BigSepL2.bigSepL2_length $$ H
  obtain ⟨e, He⟩ : ∃ e, l[j]? = some e :=
    ⟨l[j]'(by have := (List.getElem?_eq_some_iff.mp Hj).1; omega), List.getElem?_eq_getElem _⟩
  ihave #Hed := BigSepL2.bigSepL2_lookup (Φ := fun _ e o => entDataIs (GF := GF) γ e o) He Hj $$ H
  ihave #Hdep := entDataIs_deposited γ e d $$ Hed
  unfold deposited
  icases Hdep with ⟨%p, #Hdq⟩
  icases ghost_map_lookup $$ Hra Hdq with %Hl
  rw [HRd] at Hl
  cases Hl

/-- The entry at a position of a log with data: its data is the list's at that position. -/
theorem entsData_lookup (γ : RaftNames) (l : List EntryM) (ods : List (Option (List w8)))
    (m : Nat) (e : EntryM) (He : l[m]? = some e) :
    ⊢ ([∗list] e;o ∈ l;ods, entDataIs (GF := GF) γ e o) -∗
      ∃ o, ⌜ods[m]? = some o⌝ ∗ entDataIs γ e o := by
  iintro #H
  ihave %Hlen := BigSepL2.bigSepL2_length $$ H
  obtain ⟨o, Ho⟩ : ∃ o, ods[m]? = some o :=
    ⟨ods[m]'(by have := (List.getElem?_eq_some_iff.mp He).1; omega), List.getElem?_eq_getElem _⟩
  ihave #Hed := BigSepL2.bigSepL2_lookup (Φ := fun _ e o => entDataIs (GF := GF) γ e o) He Ho $$ H
  iexists o
  iframe Hed
  ipureintro; exact Ho

/-- The client's log is raft's committed log: the client's half of `rLog` and the log half's
quarter agree (the register's `reg_log_committed`, 2026-10-14, stage R; here since 2026-10-16,
stage R7, shared with the server). -/
theorem rLog_committed (γ : RaftNames) (L : List EntryM) (E : CoPset)
    (HE : ↑raftLogN ⊆ E) :
    ⊢ raftCommitInv γ -∗ rLog γ L ={E}=∗ rLog γ L ∗ isCommitted γ L := by
  iintro #Hinv HrL
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose
  iunfold rLog at HrL
  ihave %HLeq := ghostVar_agree γ.reRLog P rlq L (1 : Qp).half $$ Hq1 HrL
  subst HLeq
  ihave #HPc := ownCommitted_lb γ _ $$ HP
  imod Hclose $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imodintro
  unfold rLog
  iframe HrL HPc

/-- **Registering `d` with the result predicate `Q`** (2026-10-21; the public ghost step a
client takes before proposing `d`): for a data never registered before (its fresh token), the
registry gets `d ↦ (γq, γd)`, `γq` naming `Q`, `γd` the (empty) map of `d`'s deposits. No
committed entry holds `d` yet (`ods_not_fresh`), so the slot starts with no result. -/
theorem prop_register (γ : RaftNames) (E : CoPset) (d : List w8)
    (Q : List EntryM → IProp GF) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv γ -∗ propFresh γ d ={E}=∗ propIs γ d Q := by
  intro HE
  iintro #Hinv Hfr
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  have HE1 := raftRegN_of HE
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  have HE2 := raftLogN_of_diff HE
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  ihave %Heq := ghostVar_agree γ.reRLog P rlq l rlq $$ Hq1 Hq2
  subst Heq
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold propsOwn at Hprops
  icases Hprops with ⟨>Hra, Hs⟩
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  cases HRd : R !! d with
  | some p =>
    icases (BigSepM.bigSepM_delete (Φ := fun d (p : PropRec) =>
      iprop(▷ (propSlot (GF := GF) γ d p P ∗ propFresh γ d))) HRd).1 $$ Hs
      with ⟨⟨-, >Hfr'⟩, -⟩
    unfold propFresh
    ihave %Hne := ghostMapElem_ne γ.reFresh d d (DFrac.own 1) () () $$ Hfr Hfr'
    exact absurd rfl Hne
  | none =>
  unfold entsData
  icases Hds with ⟨%ods, #Hods⟩
  ihave %Hnf := ods_not_fresh γ P ods R d HRd $$ Hods Hra
  imod saved_pred_alloc Q DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := GName) with ⟨%γd, HKa⟩
  imod ghost_map_insert_persist d ((γq, γd) : PropRec) HRd $$ Hra with ⟨Hra, #Hfrag⟩
  ihave Hslot : propSlot γ d ((γq, γd) : PropRec) P $$ [HKa]
  · unfold propSlot propSlotRes
    isplitr
    · imodintro
      iintro %m %e %Hm #He
      icases entsData_lookup γ P ods m e Hm $$ Hods with ⟨%o, %Ho, #He'⟩
      ihave %Hoe := entDataIs_agree γ e o (some d) $$ He' He
      subst Hoe
      exact absurd (List.mem_of_getElem? Ho) Hnf
    iexists ∅
    iframe HKa
    iapply (BigSepM.bigSepM_empty (Φ := fun (_k : Nat) (γt : GName) =>
      depSlot (GF := GF) γ d γq γt P)).2
    iempintro
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hq1
    iexists ods
    iexact Hods
  imod Hclose2 $$ [Hq2 Hreads Hra Hs Hfr Hslot] with -
  · iexists P
    iframe Hq2
    unfold regsAt propsOwn
    inext
    iexists Std.insert R d ((γq, γd) : PropRec), RR
    iframe Hreads Hnoop Hra
    iapply (BigSepM.bigSepM_insert (Φ := fun d (p : PropRec) =>
      iprop(propSlot (GF := GF) γ d p P ∗ propFresh γ d)) HRd).2
    iframe Hslot Hfr
    iexact Hs
  imodintro
  unfold propIs
  iexists ((γq, γd) : PropRec)
  iframe Hfrag Hsp

/-- A key no map holds. -/
theorem GMap.exists_fresh_nat {V : Type} (K : GMap Nat V) : ∃ k, K !! k = none := by
  obtain ⟨k, hk⟩ := Iris.Std.List.fresh K.domList
  refine ⟨k, ?_⟩
  cases h : K !! k with
  | none => rfl
  | some _ => exact absurd ((GMap.mem_dom_list K k).2 (by rw [h]; rfl)) hk

/-- **Depositing a proposal of a registered `d`** (2026-10-21; `Propose`, before the proposal
leaves the node): the client's update, with the predicate `d` was registered under, goes into a
new deposit of `d`'s slot, whose ticket (`propTk`) travels with the proposal. -/
theorem prop_deposit (γ : RaftNames) (E : CoPset) (d : List w8)
    (Q : List EntryM → IProp GF) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv γ -∗ propIs γ d Q -∗ propAu1 γ d Q ={E}=∗ propTk γ d := by
  intro HE
  iintro #Hinv #Hpi Hau
  unfold propIs
  icases Hpi with ⟨%p, #Hfrag, #Hsp⟩
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  have HE1 := raftRegN_of HE
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold propsOwn at Hprops
  icases Hprops with ⟨>Hra, Hs⟩
  icases ghost_map_lookup $$ Hra Hfrag with %HRd
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun d (p : PropRec) =>
      iprop(▷ (propSlot (GF := GF) γ d p l ∗ propFresh γ d))) HRd).1 $$ Hs with ⟨Hsl, Hsback⟩
  icases Hsl with ⟨Hsl, Hfr⟩
  iunfold propSlot at Hsl
  icases Hsl with ⟨Hres, %K, >HKa, Hdeps⟩
  obtain ⟨k, hk⟩ := GMap.exists_fresh_nat K
  imod dghostVar_alloc (GF := GF) (none : Option w64) with ⟨%γt, Htk⟩
  imod ghost_map_insert_persist k γt hk $$ HKa with ⟨HKa, #Hkf⟩
  ihave Hs := Hsback $$ [Hres HKa Hdeps Hau Hfr]
  · inext
    iframe Hfr
    unfold propSlot
    iframe Hres
    iexists Std.insert K k γt
    iframe HKa
    iapply (BigSepM.bigSepM_insert (Φ := fun (_k : Nat) (γt : GName) =>
      depSlot (GF := GF) γ d p.1 γt l) hk).2
    iframe Hdeps
    unfold depSlot
    ileft
    iexists Q
    iframe Hsp Hau
  imod Hclose2 $$ [Hq2 Hreads Hra Hs] with -
  · iexists l
    iframe Hq2
    unfold regsAt propsOwn
    inext
    iexists R, RR
    iframe Hreads Hnoop Hra
    iexact Hs
  imodintro
  unfold propTk
  iexists p, k, γt
  iframe Hfrag Hkf Htk

/-- Collecting (2026-10-14, stage R): at every committed occurrence of `d` -- an entry `e` at
position `m` of a committed log `L` holding `d` --, the update's result at the log before it
(persistent, no ticket), under two laters (the invariant it is stored in; the saved predicate
naming it). -/
theorem prop_collect (γ : RaftNames) (E : CoPset) (d : List w8)
    (Q : List EntryM → IProp GF) (L : List EntryM) (m : Nat) (e : EntryM) :
    ↑raftN ⊆ E → L[m]? = some e →
    ⊢ raftCommitInv γ -∗ propIs γ d Q -∗ isCommitted γ L -∗ entDataIs γ e (some d) ={E}=∗
      ▷ ▷ □ Q (L.take m) := by
  intro HE Hm
  unfold propIs
  iintro #Hinv ⟨%p, #Hfrag, #Hsp⟩ #HL #He
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  have HE1 := raftRegN_of HE
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  have HE2 := raftLogN_of_diff HE
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  ihave %Heq := ghostVar_agree γ.reRLog P rlq l rlq $$ Hq1 Hq2
  subst Heq
  ihave %HLP := isCommitted_prefix γ L P $$ HL HP
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold propsOwn at Hprops
  icases Hprops with ⟨>Hra, Hs⟩
  icases ghost_map_lookup $$ Hra Hfrag with %HRd
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun d (p : PropRec) =>
      iprop(▷ (propSlot (GF := GF) γ d p P ∗ propFresh γ d))) HRd).1 $$ Hs with ⟨Hsl, Hsback⟩
  ihave Hsl := (later_mono (sep_mono_left (propSlot_res γ d p P))) $$ Hsl
  icases Hsl with ⟨⟨Hsl, #Hslot⟩, Hfr⟩
  ihave Hs := Hsback $$ [Hsl Hfr]
  · inext; iframe Hsl Hfr
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imod Hclose2 $$ [Hq2 Hreads Hra Hs] with -
  · iexists P
    iframe Hq2
    unfold regsAt propsOwn
    inext
    iexists R, RR
    iframe Hreads Hnoop Hra
    iexact Hs
  imodintro
  inext
  iunfold propSlotRes at Hslot
  obtain ⟨r, rfl⟩ := HLP
  have HmL := (List.getElem?_eq_some_iff.mp Hm).1
  have HmP : (L ++ r)[m]? = some e := by rw [List.getElem?_append_left HmL]; exact Hm
  ihave #HQr := Hslot $$ %m %e %HmP He
  rw [List.take_append_of_le_length (Nat.le_of_lt HmL)]
  iunfold qRes at HQr
  icases HQr with ⟨%Q', #Hsp', #HQ'⟩
  ihave #Heq := saved_pred_agree p.1 DFrac.discard DFrac.discard Q' Q (L.take m) $$ Hsp' Hsp
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨Hiff, -⟩
  imodintro
  iapply Hiff $$ HQ'

/-- The data of a committed log's entries. -/
theorem committed_data (γ : RaftNames) (E : CoPset) (l : List EntryM) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv γ -∗ isCommitted γ l ={E}=∗
      ∃ ods, [∗list] e;o ∈ l;ods, entDataIs (GF := GF) γ e o := by
  intro HE
  iintro #Hinv #Hc
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  have HE2 := raftLogN_of HE
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose
  icases isCommitted_prefix γ l P $$ Hc HP with %Hpre
  obtain ⟨r, rfl⟩ := Hpre
  unfold entsData
  icases Hds with ⟨%odsP, #HdsP⟩
  icases (BigSepL2.bigSepL2_app_inv_left (Φ := fun _ e o => entDataIs (GF := GF) γ e o)) $$ HdsP
    with ⟨%o1, %o2, %Ho, #H1, -⟩
  imod Hclose $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists l ++ r
    iframe HP Hj Htbl Hwt Hq1
    iexists odsP
    iexact HdsP
  imodintro
  iexists o1
  iexact H1

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

/-- The protocol state a cluster's members start in (2026-10-16, stage R8b, D12): term `t`, a
follower, the log `L` committed, nothing else; `initPState` is `initPStateAt 0 []`, the
bootstrap state `bootPState L` is `initPStateAt 1 L`. -/
def initPStateAt (t : w64) (L : List EntryM) : PState :=
  { initPState with term := t, log := L, commit := W64 L.length }

theorem initPState_eq : initPState = initPStateAt (W64 0) [] := rfl

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

/-- The log ghost state of a node in the initial state, from its fresh maps; since 2026-10-16
(stage R8b) at `initPStateAt t L` for the bootstrap log `L = γ.reBoot` (with its records, and
every entry of term `1`), in either mode (2026-10-25, T-M M2a; until then static unless `L` is
empty: the boot log's conf entries need no witness, `witsB`). -/
private theorem ownLogGhost_init (γ : RaftNames) (id t : w64) (L : List EntryM)
    (γm γa γc γl γw γe : GName) :
    γ.reTerms !! id = some γm → γ.reAcks !! id = some γa → γ.reCamp !! id = some γc →
    γ.reVlogs !! id = some γl → γ.reWins !! id = some γw → γ.reEvs !! id = some γe →
    γ.reBoot = L → PlogWf base0 L → (L.length : Int) < 2 ^ 64 →
    (∀ e ∈ L, e.Term' = W64 1) → (L ≠ [] → 1 ≤ uint.Z t) →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L -∗ logRecs γ base0 L -∗
      ghostMapAuth γm 1 (∅ : GMap w64 TermRec) -∗
      ghostMapAuth γa 1 (∅ : GMap (w64 × w64) Unit) -∗
      ghostMapAuth γc 1 (∅ : GMap w64 (List EntryM × w64)) -∗
      ghostMapAuth γl 1 (∅ : GMap Nat ((w64 × Bool) × List EntryM)) -∗
      ghostMapAuth γw 1 (∅ : GMap w64 (GSet w64)) -∗
      monoListAuthOwn γe 1 ([] : List Aev) -∗
      ownLogGhost γ id (initPStateAt t L) none := by
  intro Hγm Hγa Hγc Hγl Hγw Hγe HL HwfL Hlen Hones Ht
  iintro #Hinv #Hc0 #HrL Hm Ha Hc Hl Hw He
  have HWL : uint.Z (W64 (L.length : Int)) = L.length := uint_Z_W64 _ (by omega) Hlen
  have Hcommit : (initPStateAt t L).commit = W64 (L.length : Int) := rfl
  have Hlog : (initPStateAt t L).log = L := rfl
  have Hbase : (initPStateAt t L).base = base0 := rfl
  have Hterm : (initPStateAt t L).term = t := rfl
  have Hrole : (initPStateAt t L).role = .follower := rfl
  have Hcp : cprefix [] (initPStateAt t L) = L := by
    unfold cprefix; rw [Hlog, Hcommit, List.nil_append, HWL]; simp
  unfold ownLogGhost
  iexists γm, ∅, γa, ∅, [], γc, ∅, γl, ∅, γw, ∅
  iframe Hm Ha Hc Hl Hw Hinv
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
    unfold LogOk plogLastIndexZ
    rw [Hlog, Hbase, Hcommit, base0_index, HWL]
    exact ⟨PlogWf_wfR _ _ HwfL, Int.natCast_nonneg _, by omega⟩
  isplitr; · rw [Hlog, Hbase]; iexact HrL
  isplitr; · unfold matchedOk; rw [Hrole]; iempintro
  isplitr
  · unfold commitIn
    isplitr
    · unfold commitJ; ileft; ipureintro
      rw [Hlog, Hcommit, HL, HWL, List.nil_append]; exact ⟨Int.le_refl _, rfl⟩
    · unfold dynOn
      -- (2026-10-25, T-M M2a) in either mode: every entry below the commit index is the boot
      -- log's, which needs no witness
      iright; unfold witsB; iintro %k %Hk %Hb; exfalso
      have := Hk.2
      rw [Hcommit, HWL] at this
      rw [HL] at Hb
      simp at this
      omega
  isplitr; · unfold baseOk; ileft; ipureintro; rfl
  isplitr
  · ipureintro
    rw [Hlog, Hbase]
    refine ⟨FullOk_base0, HwfL, ?_⟩
    intro j x Hx
    rw [List.nil_append] at Hx
    refine ⟨?_, fun h => by rw [Hrole] at h; cases h⟩
    rw [Hterm]
    have := uint_Z_nonneg j
    by_cases Hj0 : uint.Z j = 0
    · have Hj : j = base0.index' := uint_Z_inj.mp (by rw [base0_index]; exact Hj0)
      subst Hj
      rw [plogTermAt_base] at Hx
      cases Hx
      rw [show uint.Z (base0 : entryID).term' = 0 from rfl]; exact uint_Z_nonneg t
    · obtain ⟨e, He, -, Hxt⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ HwfL) Hx
        (by rw [base0_index]; omega)
      have Hne : L ≠ [] := by intro h; subst h; simp at He
      rw [← Hxt, Hones e (List.mem_of_getElem? He), show uint.Z (W64 1) = 1 from rfl]
      exact Ht Hne
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
  isplitr; · rw [Hcp]; iexact Hc0
  ipureintro
  refine ⟨⟨fun h => (by rw [Hrole] at h; cases h), fun h => (by rw [Hrole] at h; cases h)⟩, ?_⟩
  rw [Hcommit, HWL, HL]; exact Int.le_refl _

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
private theorem ownRaftGhost_init (γ : RaftNames) (id t : w64) (L : List EntryM)
    (γv γm γa γc γl γw γe γlc γrq : GName) {md : Bool} (Hmode : γ.reDyn.isSome = md) :
    id ≠ W64 0 →
    γ.reVotes !! id = some γv → γ.reTerms !! id = some γm → γ.reAcks !! id = some γa →
    γ.reCamp !! id = some γc → γ.reVlogs !! id = some γl → γ.reWins !! id = some γw →
    γ.reEvs !! id = some γe → γ.reLcm !! id = some γlc → γ.reRdq !! id = some γrq →
    γ.reBoot = L → PlogWf base0 L → (L.length : Int) < 2 ^ 64 →
    (∀ e ∈ L, e.Term' = W64 1) → (L ≠ [] → 1 ≤ uint.Z t) →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L -∗ logRecs γ base0 L -∗
      rdCredInv γ -∗ rdCred γ 0 -∗
      ghostMapAuth γrq 1 (∅ : GMap w64 GName) -∗
      ghostMapAuth γv (1 : Qp).half (∅ : GMap w64 w64) -∗
      ghostMapAuth γm 1 (∅ : GMap w64 TermRec) -∗
      ghostMapAuth γa 1 (∅ : GMap (w64 × w64) Unit) -∗
      ghostMapAuth γc 1 (∅ : GMap w64 (List EntryM × w64)) -∗
      ghostMapAuth γl 1 (∅ : GMap Nat ((w64 × Bool) × List EntryM)) -∗
      ghostMapAuth γw 1 (∅ : GMap w64 (GSet w64)) -∗
      monoListAuthOwn γe 1 ([] : List Aev) -∗
      ghostMapAuth γlc 1 (∅ : GMap w64 GName) -∗
      ownRaftGhost γ id (initPStateAt t L) md := by
  intro Hnz Hγv Hγm Hγa Hγc Hγl Hγw Hγe Hγlc Hγrq HL HwfL Hlen Hones Ht
  iintro #Hinv #Hc0 #HrL #Hcinv Hcr0 Hrq Hv Hm Ha Hc Hl Hw He Hlc
  ihave Hlg := ownLogGhost_init γ id t L γm γa γc γl γw γe Hγm Hγa Hγc Hγl Hγw Hγe
    HL HwfL Hlen Hones Ht $$ Hinv Hc0 HrL Hm Ha Hc Hl Hw He
  have Hrole : (initPStateAt t L).role = .follower := rfl
  unfold ownRaftGhost
  iexists γv, ∅, none
  isplitr; · ipureintro; exact Hγv
  isplitr; · ipureintro; exact Hnz
  isplitl [Hv]; · iexact Hv
  isplitr; · ipureintro; exact ⟨fun t Ht => by simp at Ht, by simp [initPStateAt, initPState]⟩
  isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr
  · rw [show (initPStateAt t L).outbox = [] from rfl]
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · rw [show (initPStateAt t L).votes = ∅ from rfl, granted_empty]
    iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · unfold leaderWit; rw [Hrole]; iempintro
  isplitl [Hlg]; · iexact Hlg
  isplitr; · ipureintro; intro _ h; exact Hnz h.symm
  isplitr; · ipureintro; intro _; rfl
  isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr
  · ipureintro
    exact ⟨fun h => absurd Hrole h, fun h => by rw [Hrole] at h; cases h⟩
  isplitl [Hlc]
  · unfold lcmOwn
    iexists γlc, ∅
    iframe Hlc
    isplitr; · ipureintro; exact Hγlc
    isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
    isplitr; · ipureintro; intro t Ht; simp at Ht
    unfold lcmLead; rw [Hrole]; iempintro
  isplitl [Hrq Hcr0]
  · unfold rdOwn
    iexists γrq, ∅
    isplitr; · ipureintro; exact Hγrq
    isplitl [Hrq]; · iexact Hrq
    isplitr; · iapply (BigSepM.bigSepM_empty).2; iempintro
    isplitr; · ipureintro; intro t Ht; simp at Ht
    isplitr; · unfold rdLead; rw [Hrole]; ipureintro; rfl
    isplitr
    · rw [show (initPStateAt t L).rd.states = [] from rfl]; iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · rw [show (initPStateAt t L).rd.pend = [] from rfl]; iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitl [Hcr0]
    · rw [show (initPStateAt t L).rd.pend.length + rdCount (initPStateAt t L).outbox = 0 from rfl]; iexact Hcr0
    iframe Hcinv
    rw [show (initPStateAt t L).outbox = [] from rfl]; iapply msgsTks_nil
  ipureintro; exact Hmode

private theorem alloc_nodes (γ : RaftNames) (ids : GSet w64) (t : w64) (L : List EntryM)
    {md : Bool} (Hmode : γ.reDyn.isSome = md) :
    W64 0 ∉ ids →
    γ.reBoot = L → PlogWf base0 L → (L.length : Int) < 2 ^ 64 →
    (∀ e ∈ L, e.Term' = W64 1) → (L ≠ [] → 1 ≤ uint.Z t) →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L -∗ logRecs γ base0 L -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reVotes !! x = some γx⌝ ∗
        ghostMapAuth γx (1 : Qp).half (∅ : GMap w64 w64)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reTerms !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 TermRec)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reAcks !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap (w64 × w64) Unit)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reCamp !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 (List EntryM × w64))) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reVlogs !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap Nat ((w64 × Bool) × List EntryM))) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reWins !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 (GSet w64))) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reEvs !! x = some γx⌝ ∗
        monoListAuthOwn γx 1 ([] : List Aev)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reLcm !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 GName)) -∗
      ([∗map] x ↦ _u ∈ toMap ids, ∃ γx, ⌜γ.reRdq !! x = some γx⌝ ∗
        ghostMapAuth γx 1 (∅ : GMap w64 GName)) -∗
      rdCredInv γ -∗ rdCred γ 0 -∗
      [∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id (initPStateAt t L) md := by
  induction ids using GMap.map_ind with
  | h0 =>
    intro _ _ _ _ _ _
    iintro - - - - - - - - - - - - - -
    iapply (BigSepM.bigSepM_empty).2
    iempintro
  | hins x u ids Hx IH =>
    intro Hnz HL HwfL Hlen Hones Ht
    have Hxm : x ∈ (<[x := u]> ids : GSet w64) :=
      (GMap.elem_of_gset _ _).mpr (by rw [GMap.lookup_insert])
    have Hsub : ∀ y, y ∈ ids → y ∈ (<[x := u]> ids : GSet w64) := by
      intro y Hy
      rw [GMap.elem_of_gset] at Hy ⊢
      by_cases Hxy : x = y
      · subst Hxy; rw [Hx] at Hy; cases Hy
      · rw [GMap.lookup_insert_ne _ _ Hxy]; exact Hy
    iintro #Hinv #Hc0 #HrL Hv Hm Ha Hc Hl Hw He Hlc Hrq #Hcinv Hcr0
    icases (rdCred_split γ 0 0).1 $$ Hcr0 with ⟨Hcr1, Hcr0⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hrq with ⟨⟨%γrq, %Hγrq, Hrq1⟩, Hrq⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hlc with ⟨⟨%γlc, %Hγlc, Hlc1⟩, Hlc⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hv with ⟨⟨%γv, %Hγv, Hv1⟩, Hv⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hm with ⟨⟨%γm, %Hγm, Hm1⟩, Hm⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Ha with ⟨⟨%γa, %Hγa, Ha1⟩, Ha⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hc with ⟨⟨%γc, %Hγc, Hc1⟩, Hc⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hl with ⟨⟨%γl, %Hγl, Hl1⟩, Hl⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ Hw with ⟨⟨%γw, %Hγw, Hw1⟩, Hw⟩
    icases (BigSepM.bigSepM_insert Hx).1 $$ He with ⟨⟨%γe, %Hγe, He1⟩, He⟩
    iapply (BigSepM.bigSepM_insert Hx).2
    isplitl [Hv1 Hm1 Ha1 Hc1 Hl1 Hw1 He1 Hlc1 Hrq1 Hcr1]
    · iapply ownRaftGhost_init γ x t L γv γm γa γc γl γw γe γlc γrq Hmode
        (fun h => Hnz (h ▸ Hxm)) Hγv Hγm Hγa Hγc Hγl Hγw Hγe Hγlc Hγrq HL HwfL Hlen Hones Ht
        $$ Hinv Hc0 HrL Hcinv Hcr1 Hrq1 Hv1 Hm1 Ha1 Hc1 Hl1 Hw1 He1 Hlc1
    · iapply IH (fun h => Hnz (Hsub _ h)) HL HwfL Hlen Hones Ht
        $$ Hinv Hc0 HrL Hv Hm Ha Hc Hl Hw He Hlc Hrq Hcinv Hcr0

/-- What the client of a new ghost state is handed before the commit invariant exists
(2026-10-14, stage R): its half of the full committed log, the authorities of the fresh-data
tokens and of the fresh read-context tokens, and the empty log's
commit fact; it gives back the standing update `noopAu γ` (which may mention its own
invariants, so it is built once `γ` is known) and keeps `C γ`. -/
def allocClient (E : CoPset) (cfg : GSet w64) (dyn : Option ((e : GooseExts) → @DynCfg e))
    (C : RaftNames → IProp GF) : IProp GF :=
  iprop(∀ γ : RaftNames, ⌜γ.reCfg = cfg ∧ γ.reDyn = dyn⌝ -∗ isCommitted γ [] -∗ rLog γ [] -∗
    ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) -∗
    ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ={E}=∗ noopAu γ ∗ C γ)

/-- `allocClient` at the committed log `L` the cluster starts with (2026-10-16, stage R8b: the
bootstrap log; `[]` for `allocClient`, `allocClientBoot` is the static instance). Since
2026-10-18 (item 9, point 7) the continuation also learns the conf-change policy `ccOk`
(`γ.reCCOk = ccOk`): a client whose standing update admits raft's conf-change entries by the
policy (the server's, `srvCCPolicy`) needs it before the allocation returns. -/
def allocClientGen (E : CoPset) (cfg : GSet w64) (dyn : Option ((e : GooseExts) → @DynCfg e))
    (ccOk : w32 → List w8 → Prop) (L : List EntryM) (C : RaftNames → IProp GF) : IProp GF :=
  iprop(∀ γ : RaftNames, ⌜γ.reCfg = cfg ∧ γ.reDyn = dyn ∧ γ.reCCOk = ccOk ∧ γ.reBoot = L⌝ -∗
    isCommitted γ L -∗ rLog γ L -∗
    ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) -∗
    ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ={E}=∗ noopAu γ ∗ C γ)

theorem allocClient_gen (E : CoPset) (cfg : GSet w64) (dyn : Option ((e : GooseExts) → @DynCfg e))
    (ccOk : w32 → List w8 → Prop) (C : RaftNames → IProp GF) :
    allocClient (GF := GF) E cfg dyn C ⊢ allocClientGen E cfg dyn ccOk [] C := by
  unfold allocClient allocClientGen
  iintro H %γ %Hγ #Hc HrL Hf Hrf
  iapply H $$ %γ %(And.intro Hγ.1 Hγ.2.1) Hc HrL Hf Hrf

/-- What the allocation needs of the log a cluster starts with (2026-10-16, stage R8b):
`BootLogOk` with the peers forgotten -- entry `k` at term `1` and index `k + 1`, an entry of
another type than normal whose bytes decode as its type says and are admitted by the policy
`ccOk` (`RaftNames.reCCOk`, so that `entDataIs e none` holds of it). -/
def BootWf (ccOk : w32 → List w8 → Prop) (L : List EntryM) : Prop :=
  (L.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : EntryM), L[k]? = some e →
    e.Term' = W64 1 ∧ uint.Z e.Index' = (k : Int) + 1 ∧
    e.Type' ≠ W32 0 ∧ CCDecodes e.Type' e.Data' ∧ ccOk e.Type' e.Data'

theorem BootWf_nil (ccOk : w32 → List w8 → Prop) : BootWf ccOk [] :=
  ⟨by simp, fun _ _ h => by simp at h⟩

theorem BootWf.wf {ccOk : w32 → List w8 → Prop} {L : List EntryM} (H : BootWf ccOk L) :
    PlogWf base0 L := by
  intro k e Hk
  rw [base0_index]; push_cast
  have := (H.2 k e Hk).2.1
  omega

theorem BootWf.terms {ccOk : w32 → List w8 → Prop} {L : List EntryM} (H : BootWf ccOk L) :
    ∀ e ∈ L, e.Term' = W64 1 := by
  intro e He
  obtain ⟨k, Hk⟩ := List.getElem?_of_mem He
  exact (H.2 k e Hk).1

theorem BootWf.data {ccOk : w32 → List w8 → Prop} {L : List EntryM} (H : BootWf ccOk L) :
    ∀ e ∈ L, e.Type' ≠ W32 0 ∧ CCDecodes e.Type' e.Data' ∧ ccOk e.Type' e.Data' := by
  intro e He
  obtain ⟨k, Hk⟩ := List.getElem?_of_mem He
  exact (H.2 k e Hk).2.2

/-- The data of a log of raft's own entries (no client operation among them), with each
entry's `entData`. -/
theorem entsData_none (γ : RaftNames) (L : List EntryM) :
    ⊢ ⌜∀ e ∈ L, e.Type' ≠ W32 0 ∧ CCDecodes e.Type' e.Data' ∧ γ.reCCOk e.Type' e.Data'⌝ -∗
      entsData (GF := GF) γ L ∗ [∗list] e ∈ L, entData γ e := by
  induction L with
  | nil =>
    iintro -
    isplitr
    · unfold entsData; iexists []
      iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => entDataIs (GF := GF) γ e o)).2; iempintro
    · iapply (BigSepL.bigSepL_nil (Φ := fun _ e => entData (GF := GF) γ e)).2; iempintro
  | cons e L ih =>
    iintro %H
    ihave ⟨#Hd, #Hl⟩ := ih $$ %(fun e' h => H e' (List.mem_cons.mpr (Or.inr h)))
    ihave #He : entDataIs (GF := GF) γ e none $$ []
    · simp only [entDataIs, propDataIs]; iright; ipureintro; exact H e (List.mem_cons.mpr (Or.inl rfl))
    isplitr
    · unfold entsData
      icases Hd with ⟨%ods, #Hds⟩
      iexists none :: ods
      iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => entDataIs (GF := GF) γ e o)).2
      iframe He Hds
    · iapply (BigSepL.bigSepL_cons (Φ := fun _ e => entData (GF := GF) γ e)).2
      isplitr
      · unfold entData; iexists none; iexact He
      · iexact Hl

/-- **The allocation's core** (2026-10-16, stage R8b, D12): a fresh ghost state for the nodes
`ids`, each at `initPStateAt t L` -- the log `L` the cluster starts with, committed from the
start (`γ.reBoot = L`, `BootWf`: the bootstrap log, or `[]`), in either mode (`dyn`; until
2026-10-25, T-M M2a, static unless `L` is empty), the client's continuation at `L` (`allocClientGen`). The instances:
`ownRaftGhost_alloc_gen` (`[]`, either mode), `ownRaftGhost_alloc_boot` (the bootstrap log,
static). -/
theorem ownRaftGhost_alloc_core (E : CoPset) (cfg ids : GSet w64)
    (dyn : Option ((e : GooseExts) → @DynCfg e))
    -- (2026-10-15, stage N) the conf-change bytes the cluster admits
    (ccOk : w32 → List w8 → Prop)
    -- (2026-10-16, stage R8b) the log the cluster starts with, committed, and the term
    (L : List EntryM) (t : w64) (C : RaftNames → IProp GF)
    -- (D19p, 2026-10-18) the tracked bound, if any: the voters' superset, the static mode's
    (trk : Option (GSet w64)) (Htrk : ∀ T, trk = some T → cfg ⊆ T ∧ dyn = none)
    -- (2026-10-19, D21 M3) the no-snapshot mode, only with a bootstrap log
    (ns : Bool) (Hns : ns = true → L ≠ [])
    -- (2026-10-19, D22 S-a) the no-transfer mode; (2026-10-20, D22 S-c) only with a bootstrap log
    (nx : Bool) (Hnx : nx = true → L ≠ [])
    -- (2026-10-21, D22 S-r) the snapshots' data the cluster admits (`RaftNames.reSnapOkRaw`)
    (sok : List BootEntry → List w8 → Prop)
    -- (2026-10-26, D22 J2) the nodes' snapshot directories (`RaftNames.reSnapLoc`)
    (sl : w64 → Option GName) :
    -- (2026-10-14, reconfiguration stage B2) the voters are not empty: `RaftNames.reCfg_ne`
    cfg ≠ ∅ →
    W64 0 ∉ ids →
    BootWf ccOk L → (L ≠ [] → 1 ≤ uint.Z t) →
    ⊢ allocClientGen E cfg dyn ccOk L C -∗
      |={E}=> ∃ γ : RaftNames, ⌜γ.reCfg = cfg ∧ γ.reDyn = dyn ∧ γ.reCCOk = ccOk ∧ γ.reBoot = L ∧
          γ.reTracked = trk ∧ γ.reNoSnap = ns ∧ γ.reNoXfer = nx ∧ γ.reSnapOkRaw = sok ∧
          γ.reSnapLoc = sl⌝ ∗
        raftCommitInv (GF := GF) γ ∗
        isCommitted γ L ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id (initPStateAt t L) dyn.isSome) ∗
        C γ ∗
        -- (2026-10-13) every read credit
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  intro Hcne Hnz HLok Ht
  have HwfL := HLok.wf
  have Hones := HLok.terms
  have Hlen : (L.length : Int) < 2 ^ 64 := by have := HLok.1; omega
  iintro Hcl
  imod alloc_maps (GF := GF) (K := w64) (V := w64) ids with ⟨%nv, %Hnv, Hv⟩
  imod alloc_maps (GF := GF) (K := w64) (V := TermRec) ids with ⟨%nt, -, Ht⟩
  imod alloc_maps (GF := GF) (K := w64 × w64) (V := Unit) ids with ⟨%na, -, Ha⟩
  imod alloc_maps (GF := GF) (K := w64) (V := List EntryM × w64) ids with ⟨%nc, -, Hc⟩
  imod alloc_maps (GF := GF) (K := Nat) (V := (w64 × Bool) × List EntryM) ids
    with ⟨%nl, -, Hl⟩
  imod alloc_maps (GF := GF) (K := w64) (V := GSet w64) ids with ⟨%nw, -, Hw⟩
  imod alloc_evs (GF := GF) ids with ⟨%ne, He⟩
  imod alloc_maps (GF := GF) (K := w64) (V := GName) ids with ⟨%nlc, -, Hlc⟩
  imod alloc_maps (GF := GF) (K := w64) (V := GName) ids with ⟨%nrq, -, Hrq⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × List EntryM)
    with ⟨%γrd, Hrda⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := Unit) with ⟨%γrf, Hrfa⟩
  imod own_alloc ((● (2 ^ 64 - 2 : Nat) : Auth Nat) • (◯ (2 ^ 64 - 2 : Nat) : Auth Nat))
    (Auth.auth_both_valid_discrete.mpr ⟨⟨0, (Nat.add_zero _).symm⟩, trivial⟩) with ⟨%γrc, HC⟩
  icases (own_op γrc _ _).1 $$ HC with ⟨HCa, HCf⟩
  imod ownCommitted_alloc_at (GF := GF) L with ⟨%γc, Hcauth, #Hclb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := PropRec) with ⟨%γpr, Hpra⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := Unit) with ⟨%γfr, Hfra⟩
  imod ghostVar_alloc (GF := GF) L with ⟨%γcl, Hcl0⟩
  -- (2026-10-14, reconfiguration stage B4) the winners table, empty
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := WinRec) with ⟨%γtb, Htba⟩
  icases ghostVar_split γcl L (1 : Qp).half (1 : Qp).half $$ [Hcl0]
    with ⟨Hcl1, Hcl2⟩
  · rw [Qp.half_add_half]; iexact Hcl0
  obtain ⟨γ0, Hγ0⟩ : ∃ γ0 : RaftNames,
      γ0 = ⟨cfg, nv, nt, na, nc, nl, nw, ne, γc, γpr, γcl, γfr, nlc, nrq, γrd, γrf, γrc, γtb,
        dyn, ccOk, L.map BootEntry.ofEntry, Hcne, trk, Htrk, ns,
        fun h he => Hns h (List.map_eq_nil_iff.1 he), nx,
        fun h he => Hnx h (List.map_eq_nil_iff.1 he), sok, sl⟩ :=
    ⟨_, rfl⟩
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
  have e11 : γ0.reRLog = γcl := by rw [Hγ0]
  have e12 : γ0.reFresh = γfr := by rw [Hγ0]
  have e13 : γ0.reLcm = nlc := by rw [Hγ0]
  have e14 : γ0.reRdq = nrq := by rw [Hγ0]
  have e15 : γ0.reReads = γrd := by rw [Hγ0]
  have e15' : γ0.reRdFresh = γrf := by rw [Hγ0]
  have e16 : γ0.reRdCred = γrc := by rw [Hγ0]
  have e17 : γ0.reTbl = γtb := by rw [Hγ0]
  have eB : γ0.reBoot = L := by
    unfold RaftNames.reBoot; rw [Hγ0]; exact BootEntry.map_toEntry_ofEntry L
  have eD : γ0.reDyn = dyn := by rw [Hγ0]
  have eCC : γ0.reCCOk = ccOk := by rw [Hγ0]
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e11, ← e12, ← e13, ← e14,
    ← e15, ← e15', ← e16, ← e17]
  ihave #Hc0 : isCommitted (GF := GF) γ0 L $$ []
  · rw [isCommitted_unseal]; unfold isCommittedDef; iexact Hclb
  -- the entries' data (the bootstrap log's: conf changes the policy admits), and the records
  ihave ⟨#Hds, #Hents⟩ := entsData_none γ0 L $$ %(by rw [eCC]; exact HLok.data)
  ihave #HrL : logRecs (GF := GF) γ0 base0 L $$ []
  · iapply logRecs_boot_intro γ0 L eB HwfL Hlen Hones $$ Hents
  -- the client's part: its standing update
  iunfold allocClientGen at Hcl
  imod Hcl $$ %γ0 [] Hc0 [Hcl2] Hfra Hrfa with ⟨#Hnoop, HCl⟩
  · ipureintro; exact ⟨e0, eD, eCC, eB⟩
  · unfold rLog; iexact Hcl2
  imod inv_alloc rdCredN E iprop(∃ B : Nat, own γ0.reRdCred (● B : Auth Nat) ∗
      ⌜B < 2 ^ 64 - 1⌝) $$ [HCa] with #Hcinv
  · inext
    iexists 2 ^ 64 - 2
    iframe HCa
    ipureintro; omega
  ihave #Hcinv' : rdCredInv (GF := GF) γ0 $$ []
  · unfold rdCredInv; iexact Hcinv
  ihave Hcr : rdCred (GF := GF) γ0 (0 + (2 ^ 64 - 2)) $$ [HCf]
  · unfold rdCred; rw [Nat.zero_add]; iexact HCf
  icases (rdCred_split γ0 0 (2 ^ 64 - 2)).1 $$ Hcr with ⟨Hcr0, Hcr⟩
  -- each vote map: half to the node, half to the table
  ihave Hv2 : ([∗map] x ↦ _u ∈ toMap ids,
      iprop((∃ γx, ⌜γ0.reVotes !! x = some γx⌝ ∗
          ghostMapAuth (GF := GF) γx (1 : Qp).half (∅ : GMap w64 w64)) ∗
        (∃ γx, ⌜γ0.reVotes !! x = some γx⌝ ∗
          ghostMapAuth (GF := GF) γx (1 : Qp).half (∅ : GMap w64 w64)))) $$ [Hv]
  · iapply BigSepM.bigSepM_impl $$ Hv
    imodintro
    iintro %x %u %_ ⟨%γx, %Hx, Hax⟩
    icases (ghostMapAuth_halves γx _).1 $$ Hax with ⟨Ha1, Ha2⟩
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
  icases rlq_split γ0 L $$ Hcl1 with ⟨Hq1, Hq2⟩
  imod inv_alloc raftLogN E (raftLogInvBody γ0) $$ [Hcauth Htbl Hq1 Htba] with #Hinv
  · inext
    unfold raftLogInvBody
    iexists L
    isplitl [Hcauth]
    · rw [ownCommitted_unseal]; unfold ownCommittedDef; iexact Hcauth
    isplitr
    · unfold committedJust; ileft; ipureintro; rw [eB]; exact ⟨rfl, HwfL⟩
    isplitl [Htbl]; · iexact Htbl
    isplitl [Htba]
    · unfold winTbl
      iexists ∅
      iframe Htba
      iapply (BigSepM.bigSepM_empty).2; iempintro
    unfold logRest
    iframe Hq1 Hds
  imod inv_alloc raftRegN E (regsOwn γ0) $$ [Hq2 Hpra Hrda] with #Hreg
  · inext
    unfold regsOwn regsAt propsOwn readsReg
    iexists L
    iframe Hq2
    iexists ∅, ∅
    iframe Hpra Hrda Hnoop
    isplitl
    · iapply (BigSepM.bigSepM_empty).2; iempintro
    · iapply (BigSepM.bigSepM_empty).2; iempintro
  ihave #Hinv' : raftCommitInv (GF := GF) γ0 $$ []
  · unfold raftCommitInv raftLogInv raftRegInv; iframe Hinv Hreg
  imodintro
  iexists γ0
  isplitr; · ipureintro; exact ⟨e0, eD, eCC, eB, by rw [Hγ0], by rw [Hγ0], by rw [Hγ0], by rw [Hγ0],
    by rw [Hγ0]⟩
  isplitr; · iexact Hinv'
  isplitr; · iexact Hc0
  isplitl [Hv Ht Ha Hc Hl Hw He Hlc Hrq Hcr0]
  · iapply alloc_nodes γ0 ids t L (by rw [Hγ0]) Hnz eB HwfL Hlen Hones Ht
      $$ Hinv' Hc0 HrL Hv Ht Ha Hc Hl Hw He Hlc Hrq Hcinv' Hcr0
  iframe HCl Hcr Hcinv'


/-- The allocation, in either mode (2026-10-14, stage B5: `dyn` is the ghost state's mode,
`RaftNames.reDyn`; the static one is `ownRaftGhost_alloc`). Since stage R the client's part is
a continuation (`allocClient`), which builds the standing update `noopAu` the commit invariant
holds. Since 2026-10-16 (stage R8b) an instance of `ownRaftGhost_alloc_core` at the empty log. -/
theorem ownRaftGhost_alloc_gen (E : CoPset) (cfg ids : GSet w64)
    (dyn : Option ((e : GooseExts) → @DynCfg e))
    -- (2026-10-15, stage N) the conf-change bytes the cluster admits
    (ccOk : w32 → List w8 → Prop) (C : RaftNames → IProp GF) :
    -- (2026-10-14, reconfiguration stage B2) the voters are not empty: `RaftNames.reCfg_ne`
    cfg ≠ ∅ →
    W64 0 ∉ ids →
    ⊢ allocClient E cfg dyn C -∗
      -- (2026-10-19, D22 S-a) leader transfer on (`RaftNames.reNoXfer`)
      |={E}=> ∃ γ : RaftNames, ⌜γ.reCfg = cfg ∧ γ.reDyn = dyn ∧ γ.reCCOk = ccOk ∧
          γ.reNoXfer = false⌝ ∗
        raftCommitInv (GF := GF) γ ∗
        isCommitted γ [] ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id initPState dyn.isSome) ∗
        C γ ∗
        -- (2026-10-13) every read credit
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  intro Hcne Hnz
  iintro Hcl
  ihave Hcl' := allocClient_gen E cfg dyn ccOk C $$ Hcl
  imod ownRaftGhost_alloc_core E cfg ids dyn ccOk [] (W64 0) C none (fun _ h => by cases h)
    false (fun h => by cases h) false (fun h => by cases h) (fun _ _ => True) (fun _ => none) Hcne Hnz
    (BootWf_nil _)
    (fun h => absurd rfl h) $$ Hcl' with ⟨%γ, %Hγ, H⟩
  imodintro
  iexists γ
  isplitr; · ipureintro; exact ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1, Hγ.2.2.2.2.2.2.1⟩
  rw [initPState_eq]
  iexact H

/-- (2026-10-21, D22 S-r) **The static allocation of a cluster that takes snapshots**: as
`ownRaftGhost_alloc_gen` in the static mode, at the empty log, with the snapshots' data the cluster
admits (`sok`, `RaftNames.reSnapOkRaw`; the application's relation of a committed prefix and a
snapshot's data), outside the no-snapshot and no-transfer modes and with no tracked bound. -/
theorem ownRaftGhost_alloc_snap (E : CoPset) (cfg ids : GSet w64)
    (ccOk : w32 → List w8 → Prop) (sok : List BootEntry → List w8 → Prop)
    (C : RaftNames → IProp GF) :
    cfg ≠ ∅ →
    W64 0 ∉ ids →
    ⊢ allocClient E cfg none C -∗
      |={E}=> ∃ γ : RaftNames, ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧
          γ.reNoXfer = false ∧ γ.reNoSnap = false ∧ γ.reTracked = none ∧ γ.reSnapOkRaw = sok ∧
          -- (2026-10-26, D22 J2) no snapshot directory (`snapLocal` is `True`)
          γ.reSnapLoc = fun _ => none⌝ ∗
        raftCommitInv (GF := GF) γ ∗
        isCommitted γ [] ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id initPState) ∗
        C γ ∗
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  intro Hcne Hnz
  iintro Hcl
  ihave Hcl' := allocClient_gen E cfg none ccOk C $$ Hcl
  imod ownRaftGhost_alloc_core E cfg ids none ccOk [] (W64 0) C none (fun _ h => by cases h)
    false (fun h => by cases h) false (fun h => by cases h) sok (fun _ => none) Hcne Hnz (BootWf_nil _)
    (fun h => absurd rfl h) $$ Hcl' with ⟨%γ, %Hγ, H⟩
  imodintro
  iexists γ
  isplitr; · ipureintro; exact ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1, Hγ.2.2.2.2.2.2.1, Hγ.2.2.2.2.2.1,
    Hγ.2.2.2.2.1, Hγ.2.2.2.2.2.2.2.1, Hγ.2.2.2.2.2.2.2.2⟩
  rw [initPState_eq]
  simp only [Option.isSome_none]
  iexact H

/-! ### A new cluster's bootstrap log (2026-10-16, stage R8b, D12) -/

/-- The state every member of a new cluster is in after `RawNode.Bootstrap` (`StartNode`): term
`1`, a follower, the bootstrap log `bootLog` committed, nothing else (`initPState` otherwise). -/
def bootPState (bootLog : List EntryM) : PState :=
  { initPState with term := W64 1, log := bootLog, commit := W64 bootLog.length }

/-- The bootstrap log of the peers `ps`, as `Bootstrap` builds it: one entry per peer, entry `k`
an `EntryConfChange` (type `1`) at term `1` and index `k + 1`, whose bytes decode (`ccDecodeV1`)
to `AddNode ps[k]` and are admitted by the cluster's policy `ccOk` (`RaftNames.reCCOk`, so that
`entDataIs e none` holds of it). -/
def BootLogOk (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM) : Prop :=
  bootLog.length = ps.length ∧ (bootLog.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : EntryM), bootLog[k]? = some e →
    e.Term' = W64 1 ∧ uint.Z e.Index' = (k : Int) + 1 ∧ e.Type' = W32 1 ∧
    (∃ m : CCV1M, ccDecodeV1 e.Data' = some m ∧ m.type = W32 0 ∧ ps[k]? = some m.nodeId) ∧
    ccOk (W32 1) e.Data'

theorem bootPState_eq (bootLog : List EntryM) : bootPState bootLog = initPStateAt (W64 1) bootLog :=
  rfl

/-- Two distinct small words differ (`decide` cannot see through the instance). -/
private theorem W32_ne (a b : Int) (h0 : 0 ≤ a) (h1 : a < 2 ^ 32) (h0' : 0 ≤ b)
    (h1' : b < 2 ^ 32) (hne : a ≠ b) : (W32 a : w32) ≠ W32 b := by
  intro h
  have := congrArg uint.Z h
  rw [uint_Z_W32 a h0 h1, uint_Z_W32 b h0' h1'] at this
  exact hne this

/-- What the allocation needs of a bootstrap log. -/
theorem BootLogOk.wf {ccOk : w32 → List w8 → Prop} {ps : List w64} {bootLog : List EntryM}
    (H : BootLogOk ccOk ps bootLog) : BootWf ccOk bootLog := by
  refine ⟨H.2.1, fun k e Hk => ?_⟩
  obtain ⟨Ht, Hi, Hty, ⟨m, Hm, -, -⟩, Hok⟩ := H.2.2 k e Hk
  refine ⟨Ht, Hi, by rw [Hty]; exact W32_ne 1 0 (by omega) (by omega) (by omega) (by omega) (by omega),
    ⟨fun _ => ⟨m, Hm⟩, fun h => absurd (Hty.symm.trans h)
      (W32_ne 1 2 (by omega) (by omega) (by omega) (by omega) (by omega))⟩, ?_⟩
  rw [Hty]; exact Hok

/-- `allocClient` for a cluster starting at the bootstrap log: the client's half of the committed
log and its commit fact are at `bootLog`. -/
def allocClientBoot (E : CoPset) (cfg : GSet w64) (ccOk : w32 → List w8 → Prop)
    (bootLog : List EntryM) (C : RaftNames → IProp GF) : IProp GF :=
  iprop(∀ γ : RaftNames, ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧ γ.reBoot = bootLog⌝ -∗
    isCommitted γ bootLog -∗ rLog γ bootLog -∗
    ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) -∗
    ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ={E}=∗ noopAu γ ∗ C γ)

/-- **The allocation of a new cluster's ghost state** (stage R8b): as `ownRaftGhost_alloc`, in the
static mode, but every node at `bootPState bootLog` and the committed log `bootLog` from the start
(`BootLogOk`: the peers' conf-change entries, admitted by `ccOk`); `ownRaftGhost_alloc_core` at
the bootstrap log (2026-10-16, stage R8b). -/
theorem ownRaftGhost_alloc_boot (E : CoPset) (cfg ids : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (C : RaftNames → IProp GF)
    -- (2026-10-19, D21 M3) the no-snapshot mode (`RaftNames.reNoSnap`), or not; (D22 S-a) the
    -- no-transfer mode (`RaftNames.reNoXfer`), or not
    (ns nx : Bool)
    -- (2026-10-26, D22 J2) the members' snapshot directories (`RaftNames.reSnapLoc`)
    (sl : w64 → Option GName) :
    cfg ≠ ∅ →
    W64 0 ∉ ids →
    cfg = GMap.listToSet ps →
    BootLogOk ccOk ps bootLog →
    ⊢ allocClientBoot E cfg ccOk bootLog C -∗
      |={E}=> ∃ γ : RaftNames,
        ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧ γ.reBoot = bootLog ∧
          γ.reTracked = some cfg ∧ γ.reNoSnap = ns ∧ γ.reNoXfer = nx ∧ γ.reSnapLoc = sl⌝ ∗
        raftCommitInv (GF := GF) γ ∗
        isCommitted γ bootLog ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id (bootPState bootLog)) ∗
        C γ ∗
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  intro Hcne Hnz Hcfg Hok
  have Hbne : bootLog ≠ [] := by
    intro h
    rw [h] at Hok
    have hps : ps = [] := List.eq_nil_of_length_eq_zero Hok.1.symm
    apply Hcne
    rw [Hcfg, hps]; rfl
  iintro Hcl
  ihave Hcl' : allocClientGen (GF := GF) E cfg none ccOk bootLog C $$ [Hcl]
  · unfold allocClientGen allocClientBoot; iexact Hcl
  imod ownRaftGhost_alloc_core E cfg ids none ccOk bootLog (W64 1) C (some cfg)
    (fun T hT => by cases hT; exact ⟨GMap.subseteq_refl _, rfl⟩) ns (fun _ => Hbne) nx (fun _ => Hbne)
    (fun _ _ => True) sl Hcne Hnz Hok.wf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl' with ⟨%γ, %Hγ, H⟩
  imodintro
  iexists γ
  isplitr; · ipureintro; exact ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1, Hγ.2.2.2.1, Hγ.2.2.2.2.1, Hγ.2.2.2.2.2.1,
    Hγ.2.2.2.2.2.2.1, Hγ.2.2.2.2.2.2.2.2⟩
  rw [bootPState_eq]
  simp only [Option.isSome_none]
  iexact H

end ghost

/-! ## Derived conveniences used by `Link.lean` -/

section lemmas
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- No read credit (2026-10-13). -/
theorem rdCred_zero (γ : RaftNames) : ⊢ |==> rdCred (GF := GF) γ 0 := by
  unfold rdCred
  exact own_unit _

/-- Taking a step that consumes nothing. -/
theorem ownRaftGhost_step_0 (γ : RaftNames) (c : CfgM) (HC : CfgStatic γ c) (id : w64)
    (HT : TrackedOk γ c id) (B : Int) (HB : B < 2 ^ 64)
    (s s' : PState) :
    StepC c id B s [] s' →
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ £ 1 -∗ ownRaftGhost (GF := GF) γ id s ={⊤}=∗ ownRaftGhost γ id s' := by
  intro Hstep
  iintro #Hrc Hlc Hown
  imod rdCred_zero (GF := GF) γ with Hcr
  iapply ownRaftGhost_stepC γ c HC id HT B HB s [] s' Hstep $$ Hrc [] [Hcr] [] Hlc Hown
  · iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · rw [show rdCount ([] : List Msg) = 0 from rfl]; iexact Hcr
  · iapply msgsTks_nil

end lemmas
/-! ### The commit index never moves back (2026-10-09)

Every rule of `Step` keeps `commit` or raises it: `plogCommitTo` (`appAccept`,
`heartbeat`) takes the maximum, `commit`/`snapRestore`/`snapFastfwd` have
`commit < n` as a premise, and every other rule leaves it alone. `RawNode.Advance` needs
it to carry a queued `MsgStorageApplyResp`'s "its entries are committed" across the
steps before it. (Until 2026-10-09 `PstepCommitMono`, a premise of `Advance`'s spec.) -/

end EtcdGrove
end Perennial
