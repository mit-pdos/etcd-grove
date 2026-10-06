/-
Port of election_proof/protocol.v, lines 1426–2493 at feb5c73d4: the ghost state names,
votes, leadership, election safety, entries/acknowledgements/commitment, logs and full
logs as persistent knowledge, leaders' full logs, commitment, the global committed
log, acknowledgement histories, acknowledgements justified. (The model, lines 1–1424,
is `Protocol/Model.lean`; the rest of the ghost part is `Protocol/GhostState.lean` on.)

Ghost state

The ghost state is node-local except for one invariant: each node owns the authority
over its own histories, and that authority is the exclusive part of `ownRaftGhost`.
Everything a step needs to *learn* is persistent knowledge, so it can ride on a
message or be held across a step with nowhere to put it. The exception (2026-10-05) is
`raftCommitInv`: the authority of the one global committed log (`ownCommitted`,
`isCommitted`), with the commit fact that justifies it, and half of every node's vote
map with each vote's record (`votesTbl`) -- what `Step.commit` needs to extend the
global log (see "The global committed log" and "The commit invariant").

Election:

- `isVote γ v term cand` — node `v` voted for `cand` in `term`. Frozen into `v`'s map
  when it is allocated, so it is persistent, and unforgeable because allocating it
  takes `v`'s own authority.
- `isLeader γ id term` — a quorum of `isVote`s for `id` at `term`.

Election safety is quorum intersection plus the agreement of two `isVote`s for one
node and term; that is all `isLeader_unique` is. What holds a node to one vote per
term is `VoteHistOk`.

Replication (2026-10-01):

- `isTermLog γ v t γt` — node `v`, as leader of term `t`, keeps the entries it created
  in `t` in the ghost map `γt` (`index ↦ entry`). Frozen into `v`'s per-node map
  `reTerms` when `v` becomes leader in `t` (`Step.win`); a node is leader in a term at
  most once, and `TermsOk` is what says so.
- `isEntry γ e` — the leader of `e`'s term created `e` at `e`'s index. Two `isEntry`s
  at one `(term, index)` agree (`isEntry_agree`): the leaders agree by
  `isLeader_unique`, their term logs by the frozen map, the entries by the term
  log's.
- `isAcked γ v t i` — `v` acknowledged the leader of `t` up to `i` (frozen into `v`'s
  map `reAcks`); `i = 0` is free.
- `isCommittedIdx γ i` — a quorum acknowledged some term's leader up to at least `i`;
  `i = 0` is free.

`isMessage` attaches these to the messages that report them, and `ownRaftGhost` keeps
the leader's `isAcked` for every `Match` and `isCommittedIdx` of its commit index.

Replication safety (2026-10-02):

- The term log of `(v, t)` also records `v`'s base and log when it won `t`
  (`isTermLog γ v t γt b l0`), and holds each entry `v` creates in `t` with its
  predecessor's term: `isEntryR γ e pt`.
- `logRecs γ b es`: every entry of a log has `isEntryR` with its predecessor's term
  *in that log*. `ownLogGhost` keeps it of the node's log, with `LogOk` (well-formed in
  range, `base ≤ commit ≤ lastIndex()`). Log Matching follows from two logs' records
  alone.
- `leadPrefix γ ldr t bL l`: `l` is a log the leader of `t` had. An `app` or `snap`
  carries one, covering what it says.
- `ackAgree`: a log agrees at `i` with a `leadPrefix` of `t`. `ownLogGhost` keeps it
  (`acksOk`) of every acknowledgement a non-leader made in its current term above its
  commit index, and that a node acknowledges only at its own term (`AcksTerm`). A
  `heartbeat` carries the acknowledgement its `Commit` is bounded by. That is
  `heartbeat_commit_le_last`.

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker. Persistent/Timeless instances are proved.
* Names: iProp-valued definitions are lowerCamel (`is_vote` → `isVote`, `log_recs` →
  `logRecs`, `ack_agree` → `ackAgree`), Prop-valued ones UpperCamel (`ev_sorted` →
  `EvSorted`), lemmas keep the definition's name as written (`isLeader_unique`,
  `logRecs_agree`). (`Model.lean`'s comment at "Pure facts the replication-safety
  invariants rest on" says `LogRecs`/`AckAgree`; they are iProp-valued, so they are
  `logRecs`/`ackAgree` here, as its own `logRecs_agree` has it.) The record
  `raft_election_names` is `RaftElectionNames`, fields lowerCamel (`re_cfg` → `reCfg`).
  The inductive `aev` is `Aev`, with constructors `Aev.ack` (Rocq `AAck`) and
  `Aev.vote` (`AVote`).
* `[∗ set] x ∈ X, P x` is `[∗map] x ↦ _u ∈ toMap X, P x` (`toMap`, copied from the old
  `Protocol.lean`: `GSet` has no `[∗set]` instance). `[∗ map] k ↦ _ ∈ m` binds `_u`.
* Rocq's left-nested tuple types are kept left-nested (`(GName × entryID) × List
  raftpb.Entry`, written `((γt, b), l0)`), so the accessors `.1.1`, `.1.2`, `.2` read
  as in Rocq.
* `∀ (j : w64) (_ : P), Q` in an iProp is `∀ (j : w64), ∀ (_ : P), Q` (a BI `∀` over a
  proof of `P`), as in Rocq.
* The seals of `is_committed`/`own_committed` are `@[irreducible] def` over a `…Def`
  with a `…_unseal` theorem (Perennial's convention, e.g. `isLock`).
* `Pos.Countable` instances for `entryID`, `raftpb.Entry` and `Aev` (Rocq derives
  `Countable` for them; the ghost maps and the mono list store them) are added here.
* `ite_persistent`/`ite_timeless` (no Rocq counterpart: Rocq's `case_decide; apply _`
  inside the instance proofs) and `forall_prop_timeless` (iris-lean's `forall_timeless`
  quantifies over a `Type`, not a proof of a `Prop`) are helper instances.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.Model
import Perennial.Ghost.GhostMap
import Perennial.Ghost.MonoList
import Perennial.Ghost.SavedProp
import Perennial.Ghost.Token
import Perennial.GooseLang.Countable

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

/-- A set as the map it is (`GSet K = GMap K Unit`), for `[∗map] k ↦ _ ∈ toMap X, …`, the
`[∗ set]` of Rocq. (Copied from the old `Protocol.lean`.) -/
@[reducible] def toMap {K : Type} (X : GSet K) : GMap K Unit := X

/-! ### Countability of the data the ghost state stores (Lean addition) -/

instance entryID_countable [FfiSyntax] : Pos.Countable entryID :=
  .ofInjective (fun b => Pos.Countable.encode (b.term', b.index'))
    (by
      rintro ⟨_, _⟩ ⟨_, _⟩ h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2; rfl)

instance raftpbEntry_countable [FfiSyntax] : Pos.Countable raftpb.Entry :=
  .ofInjective (fun e => Pos.Countable.encode (e.Term', e.Index', e.Type', e.Data'))
    (by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1 h2 h3 h4; rfl)

/-- Helper instances (Rocq proves these cases with `case_decide; apply _`). -/
instance ite_persistent {PROP : Type _} [BI PROP] (c : Prop) [Decidable c] (P Q : PROP)
    [Persistent P] [Persistent Q] : Persistent (if c then P else Q) := by
  split <;> infer_instance

instance ite_timeless {PROP : Type _} [BI PROP] (c : Prop) [Decidable c] (P Q : PROP)
    [Timeless P] [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance

/-- A BI `∀` over the proofs of a proposition is timeless (iris-lean's `forall_timeless`
is for `α : Type`; Rocq's `forall_timeless` covers `∀ _ : P, Q`). -/
instance forall_prop_timeless {PROP : Type _} [BI PROP] {P : Prop} (Ψ : P → PROP)
    [∀ x, Timeless (Ψ x)] : Timeless (PROP := PROP) (BIBase.forall Ψ) where
  timeless := by
    by_cases h : P
    · have e1 : BIBase.forall Ψ ⊢ Ψ h := forall_elim h
      have e2 : Ψ h ⊢ BIBase.forall Ψ := forall_intro fun _ => .rfl
      exact (later_mono e1).trans (Timeless.timeless.trans (except0_mono e2))
    · have e2 : (True : PROP) ⊢ BIBase.forall Ψ := forall_intro fun x => absurd x h
      exact true_intro.trans (e2.trans except0_intro)

/-! ## Ghost state names -/

structure RaftElectionNames where
  /-- The voter set this ghost state is about. It lives in `γ` rather than being a
  parameter of `ownRaftGhost_step`: a step free to choose its own `cfg` could choose a
  singleton one and elect itself. -/
  reCfg : GSet w64
  /-- `reVotes !! id` names the ghost map holding node `id`'s vote history,
  `term ↦ candidate`. A node absent from here has no ghost state at all. -/
  reVotes : GMap w64 GName
  /-- `reTerms !! id`: node `id`'s map `term ↦ (γt, base, log)` of the term logs it
  allocated as leader (`isTermLog`). -/
  reTerms : GMap w64 GName
  /-- `reAcks !! id`: node `id`'s acknowledgements, `(term, index) ↦ ()`. -/
  reAcks : GMap w64 GName
  /-- `reCamp !! id`: node `id`'s campaign records, `term ↦ full log` when it started
  the election of that term (`isCamp`, 2026-10-03). -/
  reCamp : GMap w64 GName
  /-- `reVlogs !! id`: node `id`'s vote-time logs, `k ↦ (term, full log)`, one per vote
  it cast (`isVlog`, 2026-10-03). -/
  reVlogs : GMap w64 GName
  /-- `reWins !! id`: node `id`'s winning quorums, `term ↦ quorum` for each term it won
  (`isWin`, 2026-10-05). -/
  reWins : GMap w64 GName
  /-- `reEvs !! id`: node `id`'s event history, a `mono_list` of its acknowledgements
  and votes in the order it made them (`Aev`, 2026-10-05). What ties a vote to the
  acknowledgements made before it, without the node's ghost state (`ackEv`,
  `voteEv`). -/
  reEvs : GMap w64 GName
  /-- The global committed log: a `mono_list` of entries whose authority is in
  `raftCommitInv` and whose lower bounds are `isCommitted` (2026-10-05). -/
  reCommit : GName
  /-- The proposal registry: a ghost map `(term, index) ↦ (γq, γk, e0)` of the
  proposals registered by `ownRaftGhost_step_propose_reg`, whose authority is in
  `raftCommitInv` (2026-10-05). -/
  reProps : GName

/-- An event of a node's history (`reEvs`): an acknowledgement `(t, i)`, or a vote in
`T` cast knowing the leader of `T` iff `d`, with full log `F` (`isVlog`'s data). -/
inductive Aev [FfiSyntax] where
  | ack (t i : w64)
  | vote (T : w64) (d : Bool) (F : List raftpb.Entry)

section aev
variable [FfiSyntax]

instance Aev_countable : Pos.Countable Aev :=
  .ofInjective (fun
      | .ack t i => Pos.Countable.encode (Sum.inl (t, i) : (w64 × w64) ⊕ (w64 × Bool × List raftpb.Entry))
      | .vote T d F => Pos.Countable.encode (Sum.inr (T, d, F) : (w64 × w64) ⊕ (w64 × Bool × List raftpb.Entry)))
    (by
      rintro (⟨_, _⟩ | ⟨_, _, _⟩) (⟨_, _⟩ | ⟨_, _, _⟩) h <;> have h := Pos.encode_inj h <;>
        simp_all)

def aevTerm (e : Aev) : w64 :=
  match e with
  | .ack t _ => t
  | .vote T _ _ => T

/-- A node's events are in term order: it acknowledges and votes only at its own term,
which never goes down. -/
def EvSorted (L : List Aev) : Prop :=
  ∀ (p1 p2 : Nat) (e1 e2 : Aev), p1 < p2 → L[p1]? = some e1 → L[p2]? = some e2 →
    uint.Z (aevTerm e1) ≤ uint.Z (aevTerm e2)

theorem EvSorted_snoc (L : List Aev) (e : Aev) :
    EvSorted L → (∀ e', e' ∈ L → uint.Z (aevTerm e') ≤ uint.Z (aevTerm e)) →
    EvSorted (L ++ [e]) := by
  intro Hs Hle p1 p2 e1 e2 Hp H1 H2
  have Hp2 := (List.getElem?_eq_some_iff.mp H2).1
  rw [List.length_append, List.length_singleton] at Hp2
  rw [List.getElem?_append_left (by omega)] at H1
  by_cases Hlt : p2 < L.length
  · rw [List.getElem?_append_left Hlt] at H2
    exact Hs p1 p2 e1 e2 Hp H1 H2
  · rw [List.getElem?_append_right (by omega)] at H2
    have : p2 - L.length = 0 := by omega
    rw [this] at H2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at H2
    subst H2
    exact Hle e1 (List.mem_of_getElem? H1)

end aev

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF]

/-! ### Votes -/

def isVote (γ : RaftElectionNames) (v term cand : w64) : IProp GF :=
  iprop(∃ γv, ⌜γ.reVotes !! v = some γv⌝ ∗ term ↪[γv]□ cand)

instance isVote_persistent (γ : RaftElectionNames) (v term cand : w64) :
    Persistent (isVote (GF := GF) γ v term cand) := by
  unfold isVote; infer_instance

instance isVote_timeless (γ : RaftElectionNames) (v term cand : w64) :
    Timeless (isVote (GF := GF) γ v term cand) := by
  unfold isVote; infer_instance

/-- One vote per node per term. This is the other half of election safety. -/
theorem isVote_agree (γ : RaftElectionNames) (v term c1 c2 : w64) :
    ⊢ isVote (GF := GF) γ v term c1 -∗ isVote γ v term c2 -∗ ⌜c1 = c2⌝ := by
  unfold isVote
  iintro ⟨%γ1, %Hγ1, H1⟩ ⟨%γ2, %Hγ2, H2⟩
  rw [Hγ1] at Hγ2
  cases Hγ2
  iapply ghostMapElem_agree $$ H1 H2

/-! ### Leadership -/

/-- `id` won `term` with the quorum `q` of votes: frozen in `id`'s map `reWins` when it
won (`Step.win`), so the winning quorum of a term is unique (`isWin_agree`) -- which is
what tells a vote that counted in the election from one cast later, after the winner
had already replicated to the voter (pre-vote; see `voteJust`). (2026-10-05.) -/
def isWin (γ : RaftElectionNames) (id term : w64) (q : GSet w64) : IProp GF :=
  iprop(∃ γw, ⌜γ.reWins !! id = some γw ∧ IsQuorum γ.reCfg q⌝ ∗ term ↪[γw]□ q ∗
        [∗map] v ↦ _u ∈ toMap q, isVote γ v term id)

instance isWin_persistent (γ : RaftElectionNames) (id term : w64) (q : GSet w64) :
    Persistent (isWin (GF := GF) γ id term q) := by
  unfold isWin; infer_instance

instance isWin_timeless (γ : RaftElectionNames) (id term : w64) (q : GSet w64) :
    Timeless (isWin (GF := GF) γ id term q) := by
  unfold isWin; infer_instance

theorem isWin_agree (γ : RaftElectionNames) (id term : w64) (q1 q2 : GSet w64) :
    ⊢ isWin (GF := GF) γ id term q1 -∗ isWin γ id term q2 -∗ ⌜q1 = q2⌝ := by
  unfold isWin
  iintro ⟨%γ1, %H1, #F1, -⟩ ⟨%γ2, %H2, #F2, -⟩
  rw [H1.1] at H2
  obtain ⟨H2, -⟩ := H2
  cases H2
  iapply ghostMapElem_agree $$ F1 F2

def isLeader (γ : RaftElectionNames) (id term : w64) : IProp GF :=
  iprop(∃ q, isWin γ id term q)

instance isLeader_persistent (γ : RaftElectionNames) (id term : w64) :
    Persistent (isLeader (GF := GF) γ id term) := by
  unfold isLeader; infer_instance

instance isLeader_timeless (γ : RaftElectionNames) (id term : w64) :
    Timeless (isLeader (GF := GF) γ id term) := by
  unfold isLeader; infer_instance

/-! ## Election safety

Two leaders in one term were each elected by a quorum; the quorums meet in a voter that
cast one vote. -/
theorem isLeader_unique (γ : RaftElectionNames) (id1 id2 term : w64) :
    ⊢ isLeader (GF := GF) γ id1 term -∗ isLeader γ id2 term -∗ ⌜id1 = id2⌝ := by
  unfold isLeader isWin
  iintro ⟨%q1, %γ1, %Hq1, -, #H1⟩ ⟨%q2, %γ2, %Hq2, -, #H2⟩
  obtain ⟨v, Hv1, Hv2⟩ := quorums_intersect _ _ _ Hq1.2 Hq2.2
  ihave #Hv1 := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v term id1)
    ((GMap.elem_of_gset _ _).mp Hv1) $$ H1
  ihave #Hv2 := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v term id2)
    ((GMap.elem_of_gset _ _).mp Hv2) $$ H2
  iapply isVote_agree $$ Hv1 Hv2

/-! ### Entries, acknowledgements, commitment -/

/-- `v`'s term log of term `t`: the ghost map `γt`, and `v`'s compaction boundary `b` and
log `l0` (the entries after `b`) at the moment it won `t`. Neither changes while `v`
leads `t` (a leader never restores a snapshot and never truncates), so every log `v`
has in `t` is `l0` followed by entries `v` created in `t`, and `γt` holds those, each
with its predecessor's term. -/
def isTermLog (γ : RaftElectionNames) (v t : w64) (γt : GName) (b : entryID)
    (l0 : List raftpb.Entry) : IProp GF :=
  iprop(∃ γm, ⌜γ.reTerms !! v = some γm⌝ ∗
    t ↪[γm]□ (((γt, b), l0) : (GName × entryID) × List raftpb.Entry))

/-- `c`'s campaign record of term `T`: its full log (`fp ++ log`, see "Full logs") when
it became candidate in `T` -- unchanged until it wins (`campOwn`), so it is also the log
the leader of `T` started from. Frozen when allocated (`Step.campaign`); a `vote`
request carries it (`isMessage`), so the `(LogTerm, Index)` a voter checks is the last
entry of a log the candidate really had. Every term in it is below `T` (the candidate
has nothing of its own term), which is `CampOk`. (2026-10-03.) -/
def isCamp (γ : RaftElectionNames) (c T : w64) (F : List raftpb.Entry) : IProp GF :=
  iprop(∃ γc, ⌜γ.reCamp !! c = some γc ∧ CampOk T F⌝ ∗ T ↪[γc]□ F)

instance isCamp_persistent (γ : RaftElectionNames) (c T : w64) (F : List raftpb.Entry) :
    Persistent (isCamp (GF := GF) γ c T F) := by
  unfold isCamp; infer_instance

instance isCamp_timeless (γ : RaftElectionNames) (c T : w64) (F : List raftpb.Entry) :
    Timeless (isCamp (GF := GF) γ c T F) := by
  unfold isCamp; infer_instance

theorem isCamp_agree (γ : RaftElectionNames) (c T : w64) (F1 F2 : List raftpb.Entry) :
    ⊢ isCamp (GF := GF) γ c T F1 -∗ isCamp γ c T F2 -∗ ⌜F1 = F2⌝ := by
  unfold isCamp
  iintro ⟨%γ1, %H1, Hf1⟩ ⟨%γ2, %H2, Hf2⟩
  rw [H1.1] at H2
  obtain ⟨H2, -⟩ := H2
  cases H2
  iapply ghostMapElem_agree $$ Hf1 Hf2

theorem isCamp_ok (γ : RaftElectionNames) (c T : w64) (F : List raftpb.Entry) :
    ⊢ isCamp (GF := GF) γ c T F -∗ ⌜CampOk T F⌝ := by
  unfold isCamp
  iintro ⟨%_, %H, -⟩
  ipureintro; exact H.2

/-- `e` was created by the leader of its term, after an entry of term `pt`: the term log
of `e`'s term holds `(e, pt)` at `e`'s index. Since 2026-10-03 also: `e` is past the
leader's campaign log `F0`, its predecessor is `F0`'s last entry or another entry of
`e`'s term, and `pt ≤ e.term` (`PtOk`) -- which makes the terms of a log with records
non-decreasing, and lets Leader Completeness walk a log down from an entry of term `T`
to where the leader of `T` started. -/
def isEntryR (γ : RaftElectionNames) (e : raftpb.Entry) (pt : w64) : IProp GF :=
  iprop(∃ ldr γt b l0 F0, isLeader γ ldr e.Term' ∗
                 isTermLog γ ldr e.Term' γt b l0 ∗
                 isCamp γ ldr e.Term' F0 ∗
                 e.Index' ↪[γt]□ ((e, pt) : raftpb.Entry × w64) ∗
                 ⌜PtOk F0 e.Term' (uint.Z e.Index') pt⌝)

def isEntry (γ : RaftElectionNames) (e : raftpb.Entry) : IProp GF :=
  iprop(∃ pt, isEntryR γ e pt)

/-- `v`'s acknowledgement `(t, i)` is in its event history, in term order up to there
(2026-10-05). -/
def ackEv (γ : RaftElectionNames) (v t i : w64) : IProp GF :=
  iprop(∃ γe L, ⌜γ.reEvs !! v = some γe ∧ Aev.ack t i ∈ L ∧ EvSorted L⌝ ∗
          monoListLbOwn γe L)

def isAcked (γ : RaftElectionNames) (v t i : w64) : IProp GF :=
  iprop(⌜uint.Z i = 0⌝ ∨
    (∃ γa, ⌜γ.reAcks !! v = some γa⌝ ∗ (t, i) ↪[γa]□ ()) ∗ ackEv γ v t i)

instance isTermLog_persistent (γ : RaftElectionNames) (v t : w64) (γt : GName) (b : entryID)
    (l0 : List raftpb.Entry) : Persistent (isTermLog (GF := GF) γ v t γt b l0) := by
  unfold isTermLog; infer_instance
instance isTermLog_timeless (γ : RaftElectionNames) (v t : w64) (γt : GName) (b : entryID)
    (l0 : List raftpb.Entry) : Timeless (isTermLog (GF := GF) γ v t γt b l0) := by
  unfold isTermLog; infer_instance
instance isEntryR_persistent (γ : RaftElectionNames) (e : raftpb.Entry) (pt : w64) :
    Persistent (isEntryR (GF := GF) γ e pt) := by
  unfold isEntryR; infer_instance
instance isEntryR_timeless (γ : RaftElectionNames) (e : raftpb.Entry) (pt : w64) :
    Timeless (isEntryR (GF := GF) γ e pt) := by
  unfold isEntryR; infer_instance
instance isEntry_persistent (γ : RaftElectionNames) (e : raftpb.Entry) :
    Persistent (isEntry (GF := GF) γ e) := by
  unfold isEntry; infer_instance
instance isEntry_timeless (γ : RaftElectionNames) (e : raftpb.Entry) :
    Timeless (isEntry (GF := GF) γ e) := by
  unfold isEntry; infer_instance
instance ackEv_persistent (γ : RaftElectionNames) (v t i : w64) :
    Persistent (ackEv (GF := GF) γ v t i) := by
  unfold ackEv; infer_instance
instance ackEv_timeless (γ : RaftElectionNames) (v t i : w64) :
    Timeless (ackEv (GF := GF) γ v t i) := by
  unfold ackEv; infer_instance
instance isAcked_persistent (γ : RaftElectionNames) (v t i : w64) :
    Persistent (isAcked (GF := GF) γ v t i) := by
  unfold isAcked; infer_instance
instance isAcked_timeless (γ : RaftElectionNames) (v t i : w64) :
    Timeless (isAcked (GF := GF) γ v t i) := by
  unfold isAcked; infer_instance

/-- Log matching at one index: two entries with the same term and index are the same
entry. -/
theorem isTermLog_agree (γ : RaftElectionNames) (v t : w64) (γt1 : GName) (b1 : entryID)
    (l1 : List raftpb.Entry) (γt2 : GName) (b2 : entryID) (l2 : List raftpb.Entry) :
    ⊢ isTermLog (GF := GF) γ v t γt1 b1 l1 -∗ isTermLog γ v t γt2 b2 l2 -∗
      ⌜γt1 = γt2 ∧ b1 = b2 ∧ l1 = l2⌝ := by
  unfold isTermLog
  iintro ⟨%γm1, %Hγm1, Ht1⟩ ⟨%γm2, %Hγm2, Ht2⟩
  rw [Hγm1] at Hγm2
  cases Hγm2
  icases ghostMapElem_agree $$ Ht1 Ht2 with %H
  simp only [Prod.mk.injEq] at H
  ipureintro; exact ⟨H.1.1, H.1.2, H.2⟩

theorem isEntryR_agree (γ : RaftElectionNames) (e1 : raftpb.Entry) (pt1 : w64)
    (e2 : raftpb.Entry) (pt2 : w64) :
    e1.Term' = e2.Term' →
    e1.Index' = e2.Index' →
    ⊢ isEntryR (GF := GF) γ e1 pt1 -∗ isEntryR γ e2 pt2 -∗ ⌜e1 = e2 ∧ pt1 = pt2⌝ := by
  intro Ht Hi
  unfold isEntryR
  iintro ⟨%l1, %γ1, %b1, %l01, %F1, #Hl1, #Ht1, -, #He1, -⟩
    ⟨%l2, %γ2, %b2, %l02, %F2, #Hl2, #Ht2, -, #He2, -⟩
  rw [Ht]; rw [Hi]
  icases isLeader_unique γ l1 l2 e2.Term' $$ Hl1 Hl2 with %H
  subst H
  icases isTermLog_agree γ l1 e2.Term' γ1 b1 l01 γ2 b2 l02 $$ Ht1 Ht2 with %H
  obtain ⟨H, -, -⟩ := H
  subst H
  icases ghostMapElem_agree $$ He1 He2 with %H
  simp only [Prod.mk.injEq] at H
  ipureintro; exact H

theorem isEntry_agree (γ : RaftElectionNames) (e1 e2 : raftpb.Entry) :
    e1.Term' = e2.Term' →
    e1.Index' = e2.Index' →
    ⊢ isEntry (GF := GF) γ e1 -∗ isEntry γ e2 -∗ ⌜e1 = e2⌝ := by
  intro Ht Hi
  unfold isEntry
  iintro ⟨%pt1, #H1⟩ ⟨%pt2, #H2⟩
  icases isEntryR_agree γ e1 pt1 e2 pt2 Ht Hi $$ H1 H2 with %H
  ipureintro; exact H.1

/-- A snapshot's metadata `(t, i)` names an entry some leader created: the last entry the
snapshot covers. Defined through `isEntry`, not as new ghost state, so it agrees with
every other `isEntry` at `(t, i)` (`isEntry_agree`): a snapshot's compacted prefix is no
different from entries still in a log, it is only no longer stored. (2026-10-02.) -/
def isSnapMeta (γ : RaftElectionNames) (t i : w64) : IProp GF :=
  iprop(∃ e, isEntry γ e ∗ ⌜e.Term' = t ∧ e.Index' = i⌝)

instance isSnapMeta_persistent (γ : RaftElectionNames) (t i : w64) :
    Persistent (isSnapMeta (GF := GF) γ t i) := by
  unfold isSnapMeta; infer_instance
instance isSnapMeta_timeless (γ : RaftElectionNames) (t i : w64) :
    Timeless (isSnapMeta (GF := GF) γ t i) := by
  unfold isSnapMeta; infer_instance

/-- A log's base `b` names a real entry, unless it is the initial `0` (2026-10-03).
`ownLogGhost` keeps it of the node's base: the only rule that moves the base,
`Step.snapRestore`, moves it to a snapshot's metadata, which the message carries
`isSnapMeta` for. A leader whose `Storage` snapshot sits exactly at its base sends it
with `isSnapMeta` from here (`snapOk_message`); one above the base takes it from the
log's records. -/
def baseOk (γ : RaftElectionNames) (b : entryID) : IProp GF :=
  iprop(⌜uint.Z b.index' = 0⌝ ∨ isSnapMeta γ b.term' b.index')

instance baseOk_persistent (γ : RaftElectionNames) (b : entryID) :
    Persistent (baseOk (GF := GF) γ b) := by
  unfold baseOk; infer_instance
instance baseOk_timeless (γ : RaftElectionNames) (b : entryID) :
    Timeless (baseOk (GF := GF) γ b) := by
  unfold baseOk; infer_instance

/-! ### Logs as persistent knowledge (2026-10-02)

`logRecs γ b es`: every entry of the log (in range, `PlogWfR`) is `isEntryR` with its
predecessor's term *in this log*. Two logs that both have records agree wherever they
share a term at an index, all the way down (`logRecs_agree`, `plog_match_down`): that
is Log Matching, and it needs nothing but the two logs' records -- the records agree
because the term logs' fragments do.

`leadPrefix γ ldr t bL l`: `l` (after `bL`) is a log the leader `ldr` of `t` had while
leading `t`. It carries `l`'s records and, for every entry `ldr` created in `t`, the
term log's fragment -- so two `leadPrefix`es of one term agree wherever both have an
entry (`leadPrefix_agree`): both are the term log's initial log `l0` followed by
fragments of one ghost map. -/

def logRecs (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry) : IProp GF :=
  iprop([∗list] k ↦ e ∈ es,
    if uint.Z b.index' + (k : Int) + 1 < 2 ^ 64
    then iprop(∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ e pt)
    else iprop(True))

instance logRecs_persistent (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry) :
    Persistent (logRecs (GF := GF) γ b es) := by
  unfold logRecs; infer_instance
instance logRecs_timeless (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry) :
    Timeless (logRecs (GF := GF) γ b es) := by
  unfold logRecs; infer_instance

def leadFrags (γt : GName) (l0 l : List raftpb.Entry) : IProp GF :=
  iprop([∗list] k ↦ e ∈ l,
    if l0.length ≤ k then iprop(∃ pt : w64, e.Index' ↪[γt]□ ((e, pt) : raftpb.Entry × w64))
    else iprop(True))

instance leadFrags_persistent (γt : GName) (l0 l : List raftpb.Entry) :
    Persistent (leadFrags (GF := GF) γt l0 l) := by
  unfold leadFrags; infer_instance
instance leadFrags_timeless (γt : GName) (l0 l : List raftpb.Entry) :
    Timeless (leadFrags (GF := GF) γt l0 l) := by
  unfold leadFrags; infer_instance

def leadPrefix (γ : RaftElectionNames) (ldr t : w64) (bL : entryID) (l : List raftpb.Entry) :
    IProp GF :=
  iprop(isLeader γ ldr t ∗
    ∃ γt l0, isTermLog γ ldr t γt bL l0 ∗ ⌜PlogWfR bL l ∧ l0 <+: l⌝ ∗
           logRecs γ bL l ∗ leadFrags γt l0 l)

instance leadPrefix_persistent (γ : RaftElectionNames) (ldr t : w64) (bL : entryID)
    (l : List raftpb.Entry) : Persistent (leadPrefix (GF := GF) γ ldr t bL l) := by
  unfold leadPrefix; infer_instance
instance leadPrefix_timeless (γ : RaftElectionNames) (ldr t : w64) (bL : entryID)
    (l : List raftpb.Entry) : Timeless (leadPrefix (GF := GF) γ ldr t bL l) := by
  unfold leadPrefix; infer_instance

/-- One entry's record, read out of `logRecs` (Rocq: `big_sepL_lookup` + `decide_True`). -/
private theorem logRecs_elim (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry)
    (k : Nat) (e : raftpb.Entry) (Hk : es[k]? = some e)
    (Hr : uint.Z b.index' + (k : Int) + 1 < 2 ^ 64) :
    logRecs (GF := GF) γ b es ⊢
      ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ e pt := by
  unfold logRecs
  refine (BigSepL.bigSepL_lookup Hk).trans ?_
  simp only [Hr, ite_true]
  exact .rfl

/-- `logRecs` from a persistent resource giving each in-range entry's record
(Rocq: `big_sepL_intro` + `case_decide`). -/
private theorem logRecs_intro (γ : RaftElectionNames) (P : IProp GF) [Persistent P]
    (b : entryID) (es : List raftpb.Entry)
    (H : ∀ (k : Nat) (e : raftpb.Entry), es[k]? = some e →
      uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
      P ⊢ ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ e pt) :
    P ⊢ logRecs γ b es := by
  haveI : Intuitionistic P := ⟨intuitionistic_alias⟩
  unfold logRecs
  refine BigSepL.bigSepL_intro fun k e Hk => ?_
  split
  · exact H k e Hk ‹_›
  · exact true_intro

theorem logRecs_agree (γ : RaftElectionNames) (b1 : entryID) (es1 : List raftpb.Entry)
    (b2 : entryID) (es2 : List raftpb.Entry) :
    ⊢ logRecs (GF := GF) γ b1 es1 -∗ logRecs γ b2 es2 -∗ ⌜RecsAgree b1 es1 b2 es2⌝ := by
  iintro #H1 #H2
  by_cases HRA : RecsAgree b1 es1 b2 es2
  · ipureintro; exact HRA
  simp only [RecsAgree, Classical.not_forall] at HRA
  obtain ⟨k1, k2, e1, e2, Hk1, Hk2, Hr1, Hr2, Ht, Hi, Hne⟩ := HRA
  ihave ⟨%pt1, %Hpt1, #He1⟩ := logRecs_elim γ b1 es1 k1 e1 Hk1 Hr1 $$ H1
  ihave ⟨%pt2, %Hpt2, #He2⟩ := logRecs_elim γ b2 es2 k2 e2 Hk2 Hr2 $$ H2
  icases isEntryR_agree γ e1 pt1 e2 pt2 Ht Hi $$ He1 He2 with %H
  obtain ⟨H, H'⟩ := H
  exact absurd ⟨H, by rw [Hpt1, Hpt2, H']⟩ Hne

theorem leadPrefix_base (γ : RaftElectionNames) (L1 L2 t : w64) (b1 b2 : entryID)
    (l1 l2 : List raftpb.Entry) :
    ⊢ leadPrefix (GF := GF) γ L1 t b1 l1 -∗ leadPrefix γ L2 t b2 l2 -∗ ⌜b1 = b2⌝ := by
  unfold leadPrefix
  iintro ⟨#Hl1, %γ1, %l01, #Ht1, -⟩ ⟨#Hl2, %γ2, %l02, #Ht2, -⟩
  icases isLeader_unique γ L1 L2 t $$ Hl1 Hl2 with %H
  subst H
  icases isTermLog_agree γ L1 t γ1 b1 l01 γ2 b2 l02 $$ Ht1 Ht2 with %H
  ipureintro; exact H.2.1

theorem leadPrefix_wf (γ : RaftElectionNames) (L t : w64) (b : entryID) (l : List raftpb.Entry) :
    ⊢ leadPrefix (GF := GF) γ L t b l -∗ ⌜PlogWfR b l⌝ ∗ logRecs γ b l := by
  unfold leadPrefix
  iintro ⟨-, %_, %_, -, %Hw, #Hr, -⟩
  isplitr; · ipureintro; exact Hw.1
  iexact Hr

/-- One fragment read out of `leadFrags`, at the entry's index `i`. -/
private theorem leadFrags_elim (γt : GName) (l0 l : List raftpb.Entry) (k : Nat)
    (e : raftpb.Entry) (i : w64) (Hk : l[k]? = some e) (Hle : l0.length ≤ k)
    (Hi : e.Index' = i) :
    leadFrags (GF := GF) γt l0 l ⊢ ∃ pt : w64, i ↪[γt]□ ((e, pt) : raftpb.Entry × w64) := by
  unfold leadFrags
  refine (BigSepL.bigSepL_lookup Hk).trans ?_
  simp only [Hle, ite_true, Hi]
  exact .rfl

/-- Two logs of one term's leader agree wherever both have a term. -/
theorem leadPrefix_agree (γ : RaftElectionNames) (L1 L2 t : w64) (b : entryID)
    (l1 l2 : List raftpb.Entry) (j : w64) :
    (plogTermAt b l1 j).isSome → (plogTermAt b l2 j).isSome →
    ⊢ leadPrefix (GF := GF) γ L1 t b l1 -∗ leadPrefix γ L2 t b l2 -∗
      ⌜plogTermAt b l1 j = plogTermAt b l2 j⌝ := by
  intro Hs1 Hs2
  obtain ⟨t1, Ht1⟩ := Option.isSome_iff_exists.mp Hs1
  obtain ⟨t2, Ht2⟩ := Option.isSome_iff_exists.mp Hs2
  unfold leadPrefix
  iintro ⟨#Hl1, %γ1, %l01, #Hlog1, %Hw1, -, #Hf1⟩ ⟨#Hl2, %γ2, %l02, #Hlog2, %Hw2, -, #Hf2⟩
  icases isLeader_unique γ L1 L2 t $$ Hl1 Hl2 with %H
  subst H
  icases isTermLog_agree γ L1 t γ1 b l01 γ2 b l02 $$ Hlog1 Hlog2 with %H
  obtain ⟨H1, -, H2⟩ := H
  subst H1 H2
  have Hb := (plogTermAt_some_range _ _ _ _ Ht1).1
  by_cases Heq : uint.Z j = uint.Z b.index'
  · have : j = b.index' := uint_Z_inj.mp Heq
    subst this
    ipureintro; rw [plogTermAt_base, plogTermAt_base]
  obtain ⟨x1, Hx1, Hi1, Hxt1⟩ := plogTermAt_some_entry _ _ _ _ Hw1.1 Ht1 (by omega)
  obtain ⟨x2, Hx2, Hi2, Hxt2⟩ := plogTermAt_some_entry _ _ _ _ Hw2.1 Ht2 (by omega)
  rw [Ht1, Ht2, ← Hxt1, ← Hxt2]
  by_cases Hlt : (uint.Z j - uint.Z b.index' - 1).toNat < l01.length
  · have Hy := List.getElem?_eq_getElem Hlt
    have Hy1 := prefix_lookup_Some Hy Hw1.2
    have Hy2 := prefix_lookup_Some Hy Hw2.2
    rw [Hx1] at Hy1; rw [Hx2] at Hy2
    cases Hy1; cases Hy2
    ipureintro; rfl
  · ihave ⟨%pt1, #He1⟩ := leadFrags_elim γ1 l01 l1 _ x1 j Hx1 (by omega) Hi1 $$ Hf1
    ihave ⟨%pt2, #He2⟩ := leadFrags_elim γ1 l01 l2 _ x2 j Hx2 (by omega) Hi2 $$ Hf2
    icases ghostMapElem_agree $$ He1 He2 with %H
    simp only [Prod.mk.injEq] at H
    ipureintro; rw [H.1]


/-! ### Full logs as persistent knowledge (2026-10-03)

The records of a full log (`logRecs γ base0 F`) are those of its compacted prefix and of
its stored suffix (`logRecs_full`). From them: full logs match like stored ones
(`full_match`), their terms never go down (`recs_mono`), and below an entry of term `T`
they have `T` all the way to where `T`'s leader started (`recs_chain`). -/

theorem logRecs_full (γ : RaftElectionNames) (b : entryID) (fp es : List raftpb.Entry) :
    FullOk b fp →
    ⊢ logRecs (GF := GF) γ base0 fp -∗ logRecs γ b es -∗ logRecs γ base0 (fp ++ es) := by
  intro Hfull
  have Hlen := Hfull.1
  have key : ∀ (k : Nat) (e : raftpb.Entry), (fp ++ es)[k]? = some e →
      uint.Z (base0 : entryID).index' + (k : Int) + 1 < 2 ^ 64 →
      iprop(logRecs (GF := GF) γ base0 fp ∗ logRecs γ b es) ⊢
        ∃ pt, ⌜plogTermAt base0 (fp ++ es) (pidx base0 k) = some pt⌝ ∗ isEntryR γ e pt := by
    intro k e Hk Hr
    rw [base0_index] at Hr
    have Hpk : pidx base0 k = W64 (k : Int) := by unfold pidx; rw [base0_index, Int.zero_add]
    have HW : uint.Z (W64 (k : Int)) = k := uint_Z_W64 _ (by omega) (by omega)
    iintro ⟨#H1, #H2⟩
    rw [Hpk]
    by_cases Hlt : k < fp.length
    · rw [List.getElem?_append_left Hlt] at Hk
      ihave ⟨%pt, %Hpt, #He⟩ := logRecs_elim γ base0 fp k e Hk (by rw [base0_index]; omega) $$ H1
      iexists pt; iframe He; ipureintro
      rw [plogTermAt_app_l _ _ _ _ (by unfold plogLastIndexZ; rw [base0_index, HW]; omega)]
      rw [← Hpk]; exact Hpt
    · rw [List.getElem?_append_right (by omega)] at Hk
      ihave ⟨%pt, %Hpt, #He⟩ := logRecs_elim γ b es (k - fp.length) e Hk (by omega) $$ H2
      iexists pt; iframe He; ipureintro
      have Hp : pidx b (k - fp.length) = W64 (k : Int) := by
        unfold pidx; congr 1; omega
      rw [Hp] at Hpt
      rw [full_term_at b fp es _ Hfull (by rw [HW]; omega)]
      exact Hpt
  iintro #H1 #H2
  iapply logRecs_intro γ iprop(logRecs γ base0 fp ∗ logRecs γ b es) base0 (fp ++ es) key
  isplitl
  · iexact H1
  · iexact H2

theorem logRecs_take (γ : RaftElectionNames) (F : List raftpb.Entry) (n : Nat) :
    ⊢ logRecs (GF := GF) γ base0 F -∗ logRecs γ base0 (F.take n) := by
  have key : ∀ (k : Nat) (e : raftpb.Entry), (F.take n)[k]? = some e →
      uint.Z (base0 : entryID).index' + (k : Int) + 1 < 2 ^ 64 →
      logRecs (GF := GF) γ base0 F ⊢
        ∃ pt, ⌜plogTermAt base0 (F.take n) (pidx base0 k) = some pt⌝ ∗ isEntryR γ e pt := by
    intro k e Hk Hr
    rw [List.getElem?_take] at Hk
    split at Hk
    · rename_i Hkn
      refine (logRecs_elim γ base0 F k e Hk Hr).trans ?_
      iintro ⟨%pt, %Hpt, #He⟩
      iexists pt; iframe He; ipureintro
      rw [base0_index] at Hr
      rw [plogTermAt_take_full _ _ _ (by
        unfold pidx; rw [base0_index, Int.zero_add, uint_Z_W64 _ (by omega) (by omega)]; omega)]
      exact Hpt
    · cases Hk
  iintro #H
  iapply logRecs_intro γ _ base0 (F.take n) key
  iexact H

/-- One entry's record, read out. -/
theorem logRecs_lookup (γ : RaftElectionNames) (F : List raftpb.Entry) (k : Nat)
    (e : raftpb.Entry) :
    F[k]? = some e → (k : Int) + 1 < 2 ^ 64 →
    ⊢ logRecs (GF := GF) γ base0 F -∗
      ∃ pt, ⌜plogTermAt base0 F (W64 (k : Int)) = some pt⌝ ∗ isEntryR γ e pt := by
  intro Hk Hr
  have Hpk : pidx base0 k = W64 (k : Int) := by unfold pidx; rw [base0_index, Int.zero_add]
  iintro #H
  ihave ⟨%pt, %Hpt, #He⟩ := logRecs_elim γ base0 F k e Hk (by rw [base0_index]; omega) $$ H
  rw [Hpk] at Hpt
  iexists pt; iframe He; ipureintro; exact Hpt

theorem isEntryR_pt (γ : RaftElectionNames) (e : raftpb.Entry) (pt : w64) :
    ⊢ isEntryR (GF := GF) γ e pt -∗ ⌜uint.Z pt ≤ uint.Z e.Term'⌝ := by
  unfold isEntryR
  iintro ⟨%_, %_, %_, %_, %_, -, -, -, -, %Hok⟩
  ipureintro; exact Hok.2.1

/-- Full-log matching: two full logs with records that have the same term at `i` agree
everywhere below. -/
theorem full_match (γ : RaftElectionNames) (F1 F2 : List raftpb.Entry) (i : w64) :
    PlogWf base0 F1 → PlogWf base0 F2 →
    (plogTermAt base0 F1 i).isSome →
    plogTermAt base0 F1 i = plogTermAt base0 F2 i →
    ⊢ logRecs (GF := GF) γ base0 F1 -∗ logRecs γ base0 F2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z i →
          plogTermAt base0 F1 j = plogTermAt base0 F2 j⌝ := by
  intro Hw1 Hw2 Hs Heq
  iintro #H1 #H2
  icases logRecs_agree γ base0 F1 base0 F2 $$ H1 H2 with %HRA
  ipureintro
  intro j Hj
  have := uint_Z_nonneg j
  exact plog_match_down _ _ _ _ i (PlogWf_wfR _ _ Hw1) (PlogWf_wfR _ _ Hw2) HRA Hs Heq j
    (by rw [base0_index]; omega) (by rw [base0_index]; omega) Hj

/-- The compacted prefix of a log with records is determined by its base. -/
theorem FullOk_unique (γ : RaftElectionNames) (b : entryID) (fp1 fp2 : List raftpb.Entry) :
    FullOk b fp1 → FullOk b fp2 →
    ⊢ logRecs (GF := GF) γ base0 fp1 -∗ logRecs γ base0 fp2 -∗ ⌜fp1 = fp2⌝ := by
  intro Hf1 Hf2
  obtain ⟨Hl1, Hw1, -⟩ := id Hf1
  obtain ⟨Hl2, Hw2, -⟩ := id Hf2
  iintro #H1 #H2
  icases logRecs_agree γ base0 fp1 base0 fp2 $$ H1 H2 with %HRA
  have Hb : ∀ fp, FullOk b fp → plogTermAt base0 fp b.index' = some b.term' := by
    intro fp Hf
    rw [← List.append_nil fp, full_term_at b fp [] _ Hf (Int.le_refl _), plogTermAt_base]
  icases full_match γ fp1 fp2 b.index' Hw1 Hw2 (by rw [Hb _ Hf1]; rfl)
    (by rw [Hb _ Hf1, Hb _ Hf2]) $$ H1 H2 with %Hm
  ipureintro
  apply List.ext_getElem?
  intro k
  cases He1 : fp1[k]? with
  | none =>
    cases He2 : fp2[k]? with
    | none => rfl
    | some e2 =>
      have := (List.getElem?_eq_some_iff.mp He2).1
      have := List.getElem?_eq_none_iff.mp He1
      omega
  | some e1 =>
    cases He2 : fp2[k]? with
    | none =>
      have := (List.getElem?_eq_some_iff.mp He1).1
      have := List.getElem?_eq_none_iff.mp He2
      omega
    | some e2 =>
      have Hi1 := Hw1 _ _ He1
      have Hi2 := Hw2 _ _ He2
      rw [base0_index] at Hi1 Hi2
      have Hk := (List.getElem?_eq_some_iff.mp He1).1
      have := uint_Z_lt b.index'
      have HW : uint.Z (W64 ((k : Int) + 1)) = (k : Int) + 1 :=
        uint_Z_W64 _ (by omega) (by omega)
      have Ht := Hm (W64 ((k : Int) + 1)) (by rw [HW]; omega)
      rw [plogTermAt_lookup _ _ _ k e1 He1 (by rw [HW, base0_index]; push_cast; omega),
        plogTermAt_lookup _ _ _ k e2 He2 (by rw [HW, base0_index]; push_cast; omega)] at Ht
      simp only [Option.some.injEq] at Ht
      obtain ⟨H, -⟩ := HRA k k e1 e2 He1 He2 (by rw [base0_index]; omega)
        (by rw [base0_index]; omega) Ht (uint_Z_inj.mp (by omega))
      rw [H]

/-- The pure induction of `recs_mono`: each entry's predecessor term is at most its own. -/
private theorem recs_mono_pure (F : List raftpb.Entry) :
    PlogWf base0 F →
    (∀ (k : Nat) (e : raftpb.Entry), F[k]? = some e →
      ∃ pt, plogTermAt base0 F (W64 (k : Int)) = some pt ∧ uint.Z pt ≤ uint.Z e.Term') →
    ∀ (j k x y : w64), uint.Z j ≤ uint.Z k →
      plogTermAt base0 F j = some x → plogTermAt base0 F k = some y →
      uint.Z x ≤ uint.Z y := by
  intro Hwf Hstep j k x y Hjk Hx Hy
  suffices H : ∀ (d : Nat) (k y : w64), (uint.Z k - uint.Z j).toNat = d →
      uint.Z j ≤ uint.Z k → plogTermAt base0 F k = some y → uint.Z x ≤ uint.Z y from
    H _ k y rfl Hjk Hy
  intro d
  induction d with
  | zero =>
    intro k y Hd Hjk Hy
    have : j = k := uint_Z_inj.mp (by omega)
    subst this
    rw [Hx] at Hy; cases Hy; omega
  | succ d IH =>
    intro k y Hd Hjk Hy
    have := uint_Z_nonneg j
    have := uint_Z_lt k
    obtain ⟨e, He, -, Het⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ Hwf) Hy
      (by rw [base0_index]; omega)
    rw [base0_index] at He
    obtain ⟨pt, Hpt, Hle⟩ := Hstep _ _ He
    have HW : uint.Z (W64 (((uint.Z k - 0 - 1).toNat : Nat) : Int)) = uint.Z k - 1 := by
      rw [uint_Z_W64 (((uint.Z k - 0 - 1).toNat : Nat) : Int) (by omega) (by omega)]; omega
    have := IH _ pt (by rw [HW]; omega) (by rw [HW]; omega) Hpt
    rw [← Het]; omega

/-- Terms in a full log with records never go down. -/
theorem recs_mono (γ : RaftElectionNames) (F : List raftpb.Entry) :
    PlogWf base0 F →
    ⊢ logRecs (GF := GF) γ base0 F -∗
      ⌜∀ (j k x y : w64), uint.Z j ≤ uint.Z k →
          plogTermAt base0 F j = some x → plogTermAt base0 F k = some y →
          uint.Z x ≤ uint.Z y⌝ := by
  intro Hwf
  iintro #H
  have Hrng := PlogWf_range _ _ Hwf
  unfold plogLastIndexZ at Hrng; rw [base0_index] at Hrng
  by_cases Hstep : ∀ (k : Nat) (e : raftpb.Entry), F[k]? = some e →
      ∃ pt, plogTermAt base0 F (W64 (k : Int)) = some pt ∧ uint.Z pt ≤ uint.Z e.Term'
  · ipureintro; exact recs_mono_pure F Hwf Hstep
  simp only [Classical.not_forall] at Hstep
  obtain ⟨k, e, Hk, Hne⟩ := Hstep
  have Hlt := (List.getElem?_eq_some_iff.mp Hk).1
  ihave ⟨%pt, %Hpt, #He⟩ := logRecs_lookup γ F k e Hk (by omega) $$ H
  icases isEntryR_pt γ e pt $$ He with %Hle
  exact absurd ⟨pt, Hpt, Hle⟩ Hne

/-- The pure induction of `recs_chain`. -/
private theorem recs_chain_pure (F : List raftpb.Entry) (T : w64) (F0 : List raftpb.Entry) :
    PlogWf base0 F →
    (∀ (k : Nat) (e : raftpb.Entry), F[k]? = some e → e.Term' = T →
      plogLastIndexZ base0 F0 < (k : Int) + 1 ∧
      ((k : Int) + 1 = plogLastIndexZ base0 F0 + 1 →
        plogTermAt base0 F (W64 (k : Int)) = some (plogLast base0 F0).term') ∧
      (plogLastIndexZ base0 F0 + 1 < (k : Int) + 1 →
        plogTermAt base0 F (W64 (k : Int)) = some T)) →
    ∀ k : w64, 0 < uint.Z k → plogTermAt base0 F k = some T →
      plogLastIndexZ base0 F0 < uint.Z k ∧
      plogTermAt base0 F (W64 (plogLastIndexZ base0 F0))
        = some (plogLast base0 F0).term' ∧
      ∀ j : w64, plogLastIndexZ base0 F0 < uint.Z j ∧ uint.Z j ≤ uint.Z k →
        plogTermAt base0 F j = some T := by
  intro Hwf Hstep k Hk0 Hk
  have HL0 := plogLastIndexZ_nonneg base0 F0
  suffices H : ∀ (d : Nat) (k : w64), (uint.Z k).toNat = d → 0 < uint.Z k →
      plogTermAt base0 F k = some T →
      plogLastIndexZ base0 F0 < uint.Z k ∧
      plogTermAt base0 F (W64 (plogLastIndexZ base0 F0))
        = some (plogLast base0 F0).term' ∧
      ∀ j : w64, plogLastIndexZ base0 F0 < uint.Z j ∧ uint.Z j ≤ uint.Z k →
        plogTermAt base0 F j = some T from H _ k rfl Hk0 Hk
  intro d
  induction d with
  | zero => intro k Hd Hk0 _; omega
  | succ d IH =>
    intro k Hd Hk0 Hk
    have := uint_Z_lt k
    obtain ⟨e, He, -, HT⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ Hwf) Hk
      (by rw [base0_index]; omega)
    rw [base0_index] at He
    obtain ⟨HL, Hfirst, Hnext⟩ := Hstep _ _ He HT
    have Hc : (((uint.Z k - 0 - 1).toNat : Nat) : Int) = uint.Z k - 1 := by omega
    rw [Hc] at HL Hfirst Hnext
    refine ⟨by omega, ?_⟩
    by_cases Hfst : uint.Z k = plogLastIndexZ base0 F0 + 1
    · refine ⟨?_, ?_⟩
      · rw [show plogLastIndexZ base0 F0 = uint.Z k - 1 by omega]
        exact Hfirst (by omega)
      · intro j Hj
        have : j = k := uint_Z_inj.mp (by omega)
        subst this; exact Hk
    · have Hn := Hnext (by omega)
      have HW : uint.Z (W64 (uint.Z k - 1)) = uint.Z k - 1 :=
        uint_Z_W64 (uint.Z k - 1) (by omega) (by omega)
      obtain ⟨-, Hb, Hall⟩ := IH (W64 (uint.Z k - 1)) (by rw [HW]; omega) (by rw [HW]; omega) Hn
      refine ⟨Hb, ?_⟩
      intro j Hj
      by_cases Hjk : uint.Z j = uint.Z k
      · have : j = k := uint_Z_inj.mp Hjk
        subst this; exact Hk
      · exact Hall j ⟨Hj.1, by rw [HW]; omega⟩

/-- Walking down from an entry of term `T`: every entry of term `T` in a full log with
records sits past the campaign log `F0` of `T`'s leader, and the one just past it
follows `F0`'s last term. -/
theorem recs_chain (γ : RaftElectionNames) (F : List raftpb.Entry) (ldr T : w64)
    (F0 : List raftpb.Entry) :
    PlogWf base0 F →
    ⊢ isLeader (GF := GF) γ ldr T -∗ isCamp γ ldr T F0 -∗ logRecs γ base0 F -∗
      ⌜∀ k : w64, 0 < uint.Z k → plogTermAt base0 F k = some T →
          plogLastIndexZ base0 F0 < uint.Z k ∧
          plogTermAt base0 F (W64 (plogLastIndexZ base0 F0))
            = some (plogLast base0 F0).term' ∧
          ∀ j : w64, plogLastIndexZ base0 F0 < uint.Z j ∧ uint.Z j ≤ uint.Z k →
            plogTermAt base0 F j = some T⌝ := by
  intro Hwf
  iintro #Hl #Hc #H
  have Hrng := PlogWf_range _ _ Hwf
  unfold plogLastIndexZ at Hrng; rw [base0_index] at Hrng
  by_cases Hstep : ∀ (k : Nat) (e : raftpb.Entry), F[k]? = some e → e.Term' = T →
      plogLastIndexZ base0 F0 < (k : Int) + 1 ∧
      ((k : Int) + 1 = plogLastIndexZ base0 F0 + 1 →
        plogTermAt base0 F (W64 (k : Int)) = some (plogLast base0 F0).term') ∧
      (plogLastIndexZ base0 F0 + 1 < (k : Int) + 1 →
        plogTermAt base0 F (W64 (k : Int)) = some T)
  · ipureintro; exact recs_chain_pure F T F0 Hwf Hstep
  simp only [Classical.not_forall] at Hstep
  obtain ⟨k, e, Hk, HT, Hne⟩ := Hstep
  have Hlt := (List.getElem?_eq_some_iff.mp Hk).1
  have Hi := Hwf _ _ Hk
  rw [base0_index] at Hi
  subst HT
  ihave ⟨%pt, %Hpt, #He⟩ := logRecs_lookup γ F k e Hk (by omega) $$ H
  unfold isEntryR
  icases He with ⟨%ldr', %γt, %b, %l0, %F0', #Hl', -, #Hc', -, %Hok⟩
  icases isLeader_unique γ ldr ldr' e.Term' $$ Hl Hl' with %H1
  subst H1
  icases isCamp_agree γ ldr e.Term' F0 F0' $$ Hc Hc' with %H2
  subst H2
  obtain ⟨H1, -, H2, H3⟩ := Hok
  rw [Hi] at H1 H2 H3
  push_cast at H1 H2 H3
  exact absurd ⟨by omega, fun Heq => by rw [Hpt, H2 (by omega)],
    fun Hgt => by rw [Hpt, H3 (by omega)]⟩ Hne

/-! ### Leaders' full logs (2026-10-03)

`lpfull γ ldr t bL l fp`: `fp` is the compacted prefix of `ldr`'s log `(bL, l)` in term
`t`, with records; the full log `fp ++ l` extends `ldr`'s campaign log of `t`, is
well-formed, and has no term above `t`. `leadFull γ t G`: `G` is the full log of a
`leadPrefix` of `t`. -/

def lpfull (γ : RaftElectionNames) (ldr t : w64) (bL : entryID) (l fp : List raftpb.Entry) :
    IProp GF :=
  iprop(∃ F0, isCamp γ ldr t F0 ∗ logRecs γ base0 fp ∗
    ⌜FullOk bL fp ∧ F0 <+: fp ++ l ∧ PlogWf bL l ∧
      ∀ (j x : w64), plogTermAt base0 (fp ++ l) j = some x → uint.Z x ≤ uint.Z t⌝)

instance lpfull_persistent (γ : RaftElectionNames) (ldr t : w64) (bL : entryID)
    (l fp : List raftpb.Entry) : Persistent (lpfull (GF := GF) γ ldr t bL l fp) := by
  unfold lpfull; infer_instance
instance lpfull_timeless (γ : RaftElectionNames) (ldr t : w64) (bL : entryID)
    (l fp : List raftpb.Entry) : Timeless (lpfull (GF := GF) γ ldr t bL l fp) := by
  unfold lpfull; infer_instance

def leadFull (γ : RaftElectionNames) (t : w64) (G : List raftpb.Entry) : IProp GF :=
  iprop(∃ ldr bL l fp, leadPrefix γ ldr t bL l ∗ lpfull γ ldr t bL l fp ∗ ⌜G = fp ++ l⌝)

instance leadFull_persistent (γ : RaftElectionNames) (t : w64) (G : List raftpb.Entry) :
    Persistent (leadFull (GF := GF) γ t G) := by
  unfold leadFull; infer_instance
instance leadFull_timeless (γ : RaftElectionNames) (t : w64) (G : List raftpb.Entry) :
    Timeless (leadFull (GF := GF) γ t G) := by
  unfold leadFull; infer_instance

theorem leadFull_intro (γ : RaftElectionNames) (ldr t : w64) (bL : entryID)
    (l fp : List raftpb.Entry) :
    ⊢ leadPrefix (GF := GF) γ ldr t bL l -∗ lpfull γ ldr t bL l fp -∗
      leadFull γ t (fp ++ l) := by
  unfold leadFull
  iintro #H1 #H2
  iexists ldr, bL, l, fp
  iframe H1 H2; ipureintro; rfl

theorem leadFull_wf (γ : RaftElectionNames) (t : w64) (G : List raftpb.Entry) :
    ⊢ leadFull (GF := GF) γ t G -∗
      ⌜PlogWf base0 G ∧ ∀ (j x : w64), plogTermAt base0 G j = some x → uint.Z x ≤ uint.Z t⌝ ∗
      logRecs γ base0 G := by
  unfold leadFull lpfull
  iintro ⟨%ldr, %bL, %l, %fp, #Hp, ⟨%F0, -, #Hfr, %Hpure⟩, %HG⟩
  subst HG
  obtain ⟨Hfull, -, Hwf, Ht⟩ := Hpure
  ihave ⟨-, #Hr⟩ := leadPrefix_wf γ ldr t bL l $$ Hp
  isplitr
  · ipureintro; exact ⟨full_wf _ _ _ Hfull Hwf, Ht⟩
  · iapply logRecs_full γ bL fp l Hfull $$ Hfr Hr

theorem leadFull_camp (γ : RaftElectionNames) (t : w64) (G : List raftpb.Entry) :
    ⊢ leadFull (GF := GF) γ t G -∗
      ∃ ldr F0, isLeader γ ldr t ∗ isCamp γ ldr t F0 ∗ ⌜F0 <+: G⌝ := by
  unfold leadFull lpfull leadPrefix
  iintro ⟨%ldr, %bL, %l, %fp, ⟨#Hl, -⟩, ⟨%F0, #Hc, -, %Hpure⟩, %HG⟩
  subst HG
  iexists ldr, F0
  iframe Hl Hc; ipureintro; exact Hpure.2.1

/-- Two full logs of one term's leader agree wherever both have a term. -/
theorem leadFull_agree (γ : RaftElectionNames) (t : w64) (G1 G2 : List raftpb.Entry) (j : w64) :
    (plogTermAt base0 G1 j).isSome → (plogTermAt base0 G2 j).isSome →
    ⊢ leadFull (GF := GF) γ t G1 -∗ leadFull γ t G2 -∗
      ⌜plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  intro Hs1 Hs2
  iintro #H1 #H2
  ihave ⟨%Hw1, #Hr1⟩ := leadFull_wf γ t G1 $$ H1
  ihave ⟨%Hw2, #Hr2⟩ := leadFull_wf γ t G2 $$ H2
  unfold leadFull lpfull
  icases H1 with ⟨%ldr1, %bL1, %l1, %fp1, #Hp1, ⟨%F1, -, -, %Hf1⟩, %HG1⟩
  icases H2 with ⟨%ldr2, %bL2, %l2, %fp2, #Hp2, ⟨%F2, -, -, %Hf2⟩, %HG2⟩
  subst HG1 HG2
  icases leadPrefix_base γ ldr1 ldr2 t bL1 bL2 l1 l2 $$ Hp1 Hp2 with %Hb
  subst Hb
  by_cases Hge : uint.Z bL1.index' ≤ uint.Z j
  · rw [full_term_at bL1 fp1 l1 j Hf1.1 Hge] at Hs1 ⊢
    rw [full_term_at bL1 fp2 l2 j Hf2.1 Hge] at Hs2 ⊢
    iapply leadPrefix_agree γ ldr1 ldr2 t bL1 l1 l2 j Hs1 Hs2 $$ Hp1 Hp2
  · have Hb1 := full_term_at bL1 fp1 l1 _ Hf1.1 (Int.le_refl _)
    have Hb2 := full_term_at bL1 fp2 l2 _ Hf2.1 (Int.le_refl _)
    rw [plogTermAt_base] at Hb1 Hb2
    icases full_match γ _ _ bL1.index' Hw1.1 Hw2.1 (by rw [Hb1]; rfl) (by rw [Hb1, Hb2])
      $$ Hr1 Hr2 with %Hm
    ipureintro; exact Hm j (by omega)

/-! ### Commitment, naming the committed log (2026-10-03)

`cq γ t n G`: a quorum acknowledged the leader of `t` up to at least `n`, and `G`, a full
log of that leader, has an entry of term `t` at `n` -- what `Step.commit` establishes.
`commitIn γ F c tm`: the full log `F` agrees, at `c`, with such a `G` for some `t ≤ tm`
with `c ≤ n`. A node keeps `commitIn` of its commit index; messages carry it of the
`Commit` they report. `isCommittedIdx γ i` forgets the log. -/

def cq (γ : RaftElectionNames) (t n : w64) (G : List raftpb.Entry) : IProp GF :=
  iprop(⌜plogTermAt base0 G n = some t⌝ ∗ leadFull γ t G ∗
    ∃ q, ⌜IsQuorum γ.reCfg q⌝ ∗
      [∗map] v ↦ _u ∈ toMap q, ∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked γ v t i')

instance cq_persistent (γ : RaftElectionNames) (t n : w64) (G : List raftpb.Entry) :
    Persistent (cq (GF := GF) γ t n G) := by
  unfold cq; infer_instance
instance cq_timeless (γ : RaftElectionNames) (t n : w64) (G : List raftpb.Entry) :
    Timeless (cq (GF := GF) γ t n G) := by
  unfold cq; infer_instance

def commitIn (γ : RaftElectionNames) (F : List raftpb.Entry) (c tm : w64) : IProp GF :=
  iprop(⌜uint.Z c = 0⌝ ∨
    ∃ t n G, cq γ t n G ∗
      ⌜uint.Z c ≤ uint.Z n ∧ uint.Z t ≤ uint.Z tm ∧
        plogTermAt base0 G c = plogTermAt base0 F c⌝)

instance commitIn_persistent (γ : RaftElectionNames) (F : List raftpb.Entry) (c tm : w64) :
    Persistent (commitIn (GF := GF) γ F c tm) := by
  unfold commitIn; infer_instance
instance commitIn_timeless (γ : RaftElectionNames) (F : List raftpb.Entry) (c tm : w64) :
    Timeless (commitIn (GF := GF) γ F c tm) := by
  unfold commitIn; infer_instance

def isCommittedIdx (γ : RaftElectionNames) (i : w64) : IProp GF :=
  iprop(⌜uint.Z i = 0⌝ ∨ ∃ t n G, ⌜uint.Z i ≤ uint.Z n⌝ ∗ cq γ t n G)

instance isCommittedIdx_persistent (γ : RaftElectionNames) (i : w64) :
    Persistent (isCommittedIdx (GF := GF) γ i) := by
  unfold isCommittedIdx; infer_instance
instance isCommittedIdx_timeless (γ : RaftElectionNames) (i : w64) :
    Timeless (isCommittedIdx (GF := GF) γ i) := by
  unfold isCommittedIdx; infer_instance

theorem isCommittedIdx_0 (γ : RaftElectionNames) : ⊢ isCommittedIdx (GF := GF) γ (W64 0) := by
  unfold isCommittedIdx
  ileft; ipureintro; rfl

/-- What is committed up to `i` is committed up to anything below. -/
theorem isCommittedIdx_le (γ : RaftElectionNames) (i j : w64) :
    uint.Z j ≤ uint.Z i → ⊢ isCommittedIdx (GF := GF) γ i -∗ isCommittedIdx γ j := by
  intro Hle
  unfold isCommittedIdx
  iintro (%H0 | ⟨%t, %n, %G, %Hi, #Hq⟩)
  · ileft; ipureintro; have := uint_Z_nonneg j; omega
  · iright; iexists t, n, G; iframe Hq; ipureintro; omega

theorem commitIn_committed (γ : RaftElectionNames) (F : List raftpb.Entry) (c tm : w64) :
    ⊢ commitIn (GF := GF) γ F c tm -∗ isCommittedIdx γ c := by
  unfold commitIn isCommittedIdx
  iintro (%H0 | ⟨%t, %n, %G, #Hq, %Hc⟩)
  · ileft; ipureintro; exact H0
  · iright; iexists t, n, G; iframe Hq; ipureintro; exact Hc.1

/-! ### The global committed log (2026-10-05)

The external face of commitment: the illusion of one global log. `isCommitted γ l` --
the list of entries `l` is a prefix of the global committed log -- is a persistent lower
bound, the only resource a client sees. `ownCommitted γ l` -- the global committed log
is `l` -- is its authority, a `mono_list` authority on `reCommit` held whole by the
internal invariant `raftCommitInv` (below, with the facts that justify the log: a quorum
of acknowledgements of one leader, and that leader's log). `Step.commit` extends it
inside a leader's `Step`; no party outside the invariant holds any of it (the leader
commits its own term's no-op with no client involved, and leadership moves between
nodes). Every `isCommitted` is a prefix of `ownCommitted` (`isCommitted_prefix`), so any
two are prefixes of one another (`isCommitted_agree`): every node's committed prefix,
every commit index a message reports, is a prefix of one log. -/

def isCommittedDef (γ : RaftElectionNames) (l : List raftpb.Entry) : IProp GF :=
  monoListLbOwn γ.reCommit l
@[irreducible] def isCommitted (γ : RaftElectionNames) (l : List raftpb.Entry) : IProp GF :=
  isCommittedDef γ l
theorem isCommitted_unseal : @isCommitted = @isCommittedDef := by
  funext; with_unfolding_all rfl

def ownCommittedDef (γ : RaftElectionNames) (l : List raftpb.Entry) : IProp GF :=
  monoListAuthOwn γ.reCommit 1 l
@[irreducible] def ownCommitted (γ : RaftElectionNames) (l : List raftpb.Entry) : IProp GF :=
  ownCommittedDef γ l
theorem ownCommitted_unseal : @ownCommitted = @ownCommittedDef := by
  funext; with_unfolding_all rfl

instance isCommitted_persistent (γ : RaftElectionNames) (l : List raftpb.Entry) :
    Persistent (isCommitted (GF := GF) γ l) := by
  rw [isCommitted_unseal]; unfold isCommittedDef; infer_instance
instance isCommitted_timeless (γ : RaftElectionNames) (l : List raftpb.Entry) :
    Timeless (isCommitted (GF := GF) γ l) := by
  rw [isCommitted_unseal]; unfold isCommittedDef; infer_instance
instance ownCommitted_timeless (γ : RaftElectionNames) (l : List raftpb.Entry) :
    Timeless (ownCommitted (GF := GF) γ l) := by
  rw [ownCommitted_unseal]; unfold ownCommittedDef; infer_instance

theorem isCommitted_agree (γ : RaftElectionNames) (l1 l2 : List raftpb.Entry) :
    ⊢ isCommitted (GF := GF) γ l1 -∗ isCommitted γ l2 -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  rw [isCommitted_unseal]; unfold isCommittedDef
  exact mono_list_lb_valid _ _ _

theorem isCommitted_mono (γ : RaftElectionNames) (l1 l2 : List raftpb.Entry) :
    l1 <+: l2 → ⊢ isCommitted (GF := GF) γ l2 -∗ isCommitted γ l1 := by
  intro Hp
  rw [isCommitted_unseal]; unfold isCommittedDef
  iintro H; iapply monoListLbOwn_le _ Hp; iexact H

theorem ownCommitted_lb (γ : RaftElectionNames) (l : List raftpb.Entry) :
    ⊢ ownCommitted (GF := GF) γ l -∗ isCommitted γ l := by
  rw [ownCommitted_unseal, isCommitted_unseal]; unfold ownCommittedDef isCommittedDef
  iintro H; iapply monoListLbOwn_get; iexact H

theorem isCommitted_prefix (γ : RaftElectionNames) (l l' : List raftpb.Entry) :
    ⊢ isCommitted (GF := GF) γ l -∗ ownCommitted γ l' -∗ ⌜l <+: l'⌝ := by
  rw [ownCommitted_unseal, isCommitted_unseal]; unfold ownCommittedDef isCommittedDef
  iintro H1 H2
  icases mono_list_auth_lb_valid $$ H2 H1 with %H
  ipureintro; exact H.2

/-- Extending the global log (inside the invariant). (Rocq `Local`; public here, since
the later modules use it.) -/
theorem ownCommitted_extend (γ : RaftElectionNames) (l l' : List raftpb.Entry) :
    l <+: l' → ⊢ ownCommitted (GF := GF) γ l ==∗ ownCommitted γ l' ∗ isCommitted γ l' := by
  intro Hp
  rw [ownCommitted_unseal, isCommitted_unseal]; unfold ownCommittedDef isCommittedDef
  exact monoListAuthOwn_update _ Hp

/-- (Rocq `Local`.) -/
theorem ownCommitted_alloc :
    ⊢ |==> ∃ γc : GName, monoListAuthOwn (GF := GF) γc 1 ([] : List raftpb.Entry) ∗
                         monoListLbOwn γc ([] : List raftpb.Entry) := by
  exact mono_list_own_alloc _

/-- Two full logs with records that agree at `c` have the same first `c` entries. -/
theorem full_take_eq (γ : RaftElectionNames) (F1 F2 : List raftpb.Entry) (c : w64) :
    PlogWf base0 F1 → PlogWf base0 F2 →
    (plogTermAt base0 F1 c).isSome →
    plogTermAt base0 F1 c = plogTermAt base0 F2 c →
    ⊢ logRecs (GF := GF) γ base0 F1 -∗ logRecs γ base0 F2 -∗
      ⌜F1.take (uint.Z c).toNat = F2.take (uint.Z c).toNat⌝ := by
  intro Hw1 Hw2 Hs Heq
  iintro #H1 #H2
  icases logRecs_agree γ base0 F1 base0 F2 $$ H1 H2 with %HRA
  icases full_match γ F1 F2 c Hw1 Hw2 Hs Heq $$ H1 H2 with %Hm
  ipureintro
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  have Hc1 := (plogTermAt_some_range _ _ _ _ Hx).2
  rw [Heq] at Hx
  have Hc2 := (plogTermAt_some_range _ _ _ _ Hx).2
  unfold plogLastIndexZ at Hc1 Hc2; rw [base0_index] at Hc1 Hc2
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take]
  by_cases Hk : k < (uint.Z c).toNat
  · simp only [Hk, ite_true]
    obtain ⟨e1, He1⟩ : ∃ e, F1[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e2, He2⟩ : ∃ e, F2[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [He1, He2]
    have Hi1 := Hw1 _ _ He1
    have Hi2 := Hw2 _ _ He2
    rw [base0_index] at Hi1 Hi2
    have := uint_Z_lt c
    have HW : uint.Z (W64 ((k : Int) + 1)) = (k : Int) + 1 :=
      uint_Z_W64 _ (by omega) (by omega)
    have Ht := Hm (W64 ((k : Int) + 1)) (by rw [HW]; omega)
    rw [plogTermAt_lookup _ _ _ k e1 He1 (by rw [HW, base0_index]; push_cast; omega),
      plogTermAt_lookup _ _ _ k e2 He2 (by rw [HW, base0_index]; push_cast; omega)] at Ht
    simp only [Option.some.injEq] at Ht
    obtain ⟨H, -⟩ := HRA k k e1 e2 He1 He2 (by rw [base0_index]; omega)
      (by rw [base0_index]; omega) Ht (uint_Z_inj.mp (by omega))
    rw [H]
  · simp only [Hk, ite_false]

theorem cq_full (γ : RaftElectionNames) (t n : w64) (G : List raftpb.Entry) :
    ⊢ cq (GF := GF) γ t n G -∗ ⌜PlogWf base0 G⌝ ∗ logRecs γ base0 G := by
  unfold cq
  iintro ⟨-, #Hf, -⟩
  icases leadFull_wf γ t G $$ Hf with ⟨%H, #Hr⟩
  isplitr; · ipureintro; exact H.1
  iexact Hr

private theorem cq_term (γ : RaftElectionNames) (t n : w64) (G : List raftpb.Entry) :
    cq (GF := GF) γ t n G ⊢ ⌜plogTermAt base0 G n = some t⌝ := by
  unfold cq
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-- `commitIn` of a full log with records holds of anything below, and of any log that
agrees with it at its commit point. -/
theorem commitIn_le (γ : RaftElectionNames) (F : List raftpb.Entry) (c c' tm : w64) :
    PlogWf base0 F → uint.Z c' ≤ uint.Z c →
    ⊢ logRecs (GF := GF) γ base0 F -∗ commitIn γ F c tm -∗ commitIn γ F c' tm := by
  intro Hwf Hle
  unfold commitIn
  iintro #Hr (%H0 | ⟨%t, %n, %G, #Hq, %Hc⟩)
  · ileft; ipureintro; have := uint_Z_nonneg c'; omega
  ihave ⟨%HwG, #HrG⟩ := cq_full γ t n G $$ Hq
  ihave %Hn := cq_term γ t n G $$ Hq
  have HsG : (plogTermAt base0 G c).isSome :=
    full_term_at_some G c n (by rw [Hn]; rfl) Hc.1
  icases full_match γ G F c HwG Hwf HsG Hc.2.2 $$ HrG Hr with %Hm
  iright; iexists t, n, G; iframe Hq; ipureintro
  exact ⟨by omega, Hc.2.1, Hm c' Hle⟩

theorem commitIn_agree (γ : RaftElectionNames) (F F' : List raftpb.Entry) (c tm tm' : w64) :
    uint.Z tm ≤ uint.Z tm' →
    plogTermAt base0 F' c = plogTermAt base0 F c →
    ⊢ commitIn (GF := GF) γ F c tm -∗ commitIn γ F' c tm' := by
  intro Htm Heq
  unfold commitIn
  iintro (%H0 | ⟨%t, %n, %G, #Hq, %Hc⟩)
  · ileft; ipureintro; exact H0
  · iright; iexists t, n, G; iframe Hq; ipureintro
    exact ⟨Hc.1, by omega, by rw [Heq]; exact Hc.2.2⟩

/-! ### Histories of acknowledgements (2026-10-03)

What Leader Completeness needs of a voter is that its log, at the moment it voted in
`T`, still agreed with every acknowledgement it had made in an earlier term `t` --
*unless* the leaders of the terms in between disagreed among themselves, which the
induction over terms rules out. `hist γ F t i B` says that of the full log `F` and an
acknowledgement `(t, i)`, for leaders of terms below `B`: at every index `j ≤ i`, `F` has
what some log `okL` -- of a leader of a term in `[t, B)`, or a committed log of an
earlier term -- has there; or two such logs already disagree at or below `j`. Each node
keeps `hist` of each of its acknowledgements (`ownLogGhost`); the bound `B` is `bnd s`
-- the current term, plus one when the node has a leader or is one. -/

def okL (γ : RaftElectionNames) (t : w64) (B : Int) (j : w64) (X : List raftpb.Entry) :
    IProp GF :=
  iprop((∃ t'' : w64, ⌜uint.Z t ≤ uint.Z t'' ∧ uint.Z t'' < B⌝ ∗ leadFull γ t'' X) ∨
    (∃ t'' n'' : w64, ⌜uint.Z t'' < uint.Z t ∧ uint.Z j ≤ uint.Z n''⌝ ∗ cq γ t'' n'' X))

instance okL_persistent (γ : RaftElectionNames) (t : w64) (B : Int) (j : w64)
    (X : List raftpb.Entry) : Persistent (okL (GF := GF) γ t B j X) := by
  unfold okL; infer_instance

/-- (Lean addition: Rocq's instance search unfolds `okL`/`hist` where it needs this.) -/
instance okL_timeless (γ : RaftElectionNames) (t : w64) (B : Int) (j : w64)
    (X : List raftpb.Entry) : Timeless (okL (GF := GF) γ t B j X) := by
  unfold okL; infer_instance

def hist (γ : RaftElectionNames) (F : List raftpb.Entry) (t i : w64) (B : Int) : IProp GF :=
  iprop(∀ (j : w64), ∀ (_ : 0 < uint.Z j ∧ uint.Z j ≤ uint.Z i),
    (∃ X, okL γ t B j X ∗
       ⌜(plogTermAt base0 X j).isSome ∧ plogTermAt base0 X j = plogTermAt base0 F j⌝) ∨
    (∃ (j' : w64), ∃ X1 X2, ⌜uint.Z j' ≤ uint.Z j⌝ ∗ okL γ t B j' X1 ∗ okL γ t B j' X2 ∗
       ⌜(plogTermAt base0 X1 j').isSome ∧ (plogTermAt base0 X2 j').isSome ∧
         plogTermAt base0 X1 j' ≠ plogTermAt base0 X2 j'⌝))

instance hist_persistent (γ : RaftElectionNames) (F : List raftpb.Entry) (t i : w64) (B : Int) :
    Persistent (hist (GF := GF) γ F t i B) := by
  unfold hist; infer_instance

/-- (Lean addition, as `okL_timeless`.) -/
instance hist_timeless (γ : RaftElectionNames) (F : List raftpb.Entry) (t i : w64) (B : Int) :
    Timeless (hist (GF := GF) γ F t i B) := by
  unfold hist; infer_instance

theorem okL_mono (γ : RaftElectionNames) (t : w64) (B B' : Int) (j : w64)
    (X : List raftpb.Entry) :
    B ≤ B' → ⊢ okL (GF := GF) γ t B j X -∗ okL γ t B' j X := by
  intro HB
  unfold okL
  iintro (⟨%t'', %Ht, #H⟩ | #H)
  · ileft; iexists t''; iframe H; ipureintro; omega
  · iright; iexact H

theorem okL_le (γ : RaftElectionNames) (t : w64) (B : Int) (j j' : w64) (X : List raftpb.Entry) :
    uint.Z j' ≤ uint.Z j → ⊢ okL (GF := GF) γ t B j X -∗ okL γ t B j' X := by
  intro Hj
  unfold okL
  iintro (#H | ⟨%t'', %n'', %Ht, #H⟩)
  · ileft; iexact H
  · iright; iexists t'', n''; iframe H; ipureintro; omega

theorem hist_mono (γ : RaftElectionNames) (F : List raftpb.Entry) (t i : w64) (B B' : Int) :
    B ≤ B' → ⊢ hist (GF := GF) γ F t i B -∗ hist γ F t i B' := by
  intro HB
  unfold hist
  iintro #H %j %Hj
  ihave H' := H $$ %j %Hj
  icases H' with (⟨%X, #HX, %HXj⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
  · ileft; iexists X
    isplitl
    · iapply okL_mono γ t B B' j X HB $$ HX
    · ipureintro; exact HXj
  · iright; iexists j', X1, X2
    isplitl
    · ipureintro; exact Hj'
    isplitl
    · iapply okL_mono γ t B B' j' X1 HB $$ H1
    isplitl
    · iapply okL_mono γ t B B' j' X2 HB $$ H2
    · ipureintro; exact Hd

/-- A log that keeps every term `F` has keeps its histories. -/
theorem hist_keep (γ : RaftElectionNames) (F F' : List raftpb.Entry) (t i : w64) (B : Int) :
    (∀ j : w64, 0 < uint.Z j ∧ uint.Z j ≤ uint.Z i → (plogTermAt base0 F j).isSome →
       plogTermAt base0 F' j = plogTermAt base0 F j) →
    ⊢ hist (GF := GF) γ F t i B -∗ hist γ F' t i B := by
  intro Hk
  unfold hist
  iintro #H %j %Hj
  ihave H' := H $$ %j %Hj
  icases H' with (⟨%X, #HX, %HXj⟩ | #Hc)
  · ileft; iexists X; iframe HX; ipureintro
    obtain ⟨Hs, HXj⟩ := HXj
    refine ⟨Hs, ?_⟩
    rw [HXj, Hk j Hj (by rw [← HXj]; exact Hs)]
  · iright; iexact Hc

/-- The log of an `okL` is a full log with records. -/
private theorem okL_full (γ : RaftElectionNames) (t : w64) (B : Int) (j : w64)
    (X : List raftpb.Entry) :
    okL (GF := GF) γ t B j X ⊢ ⌜PlogWf base0 X⌝ ∗ logRecs γ base0 X := by
  unfold okL
  iintro (⟨%t'', -, #Hf⟩ | ⟨%t'', %n'', -, #Hq⟩)
  · ihave ⟨%H, #Hr⟩ := leadFull_wf γ t'' X $$ Hf
    isplitr
    · ipureintro; exact H.1
    · iexact Hr
  · iapply cq_full γ t'' n'' X $$ Hq

/-- A full log that agrees with `okL`-log `X` at `i` has a history of `(t, i)`. -/
theorem hist_of_agree (γ : RaftElectionNames) (F X : List raftpb.Entry) (t i : w64) (B : Int) :
    PlogWf base0 F →
    (plogTermAt base0 X i).isSome → plogTermAt base0 X i = plogTermAt base0 F i →
    ⊢ logRecs (GF := GF) γ base0 F -∗ okL γ t B i X -∗ hist γ F t i B := by
  intro HwF Hs Heq
  iintro #HrF #HX
  ihave ⟨%HwX, #HrX⟩ := okL_full γ t B i X $$ HX
  icases full_match γ X F i HwX HwF Hs Heq $$ HrX HrF with %Hm
  unfold hist
  iintro %j %Hj
  ileft; iexists X
  isplitl
  · iapply okL_le γ t B i j X Hj.2 $$ HX
  · ipureintro; exact ⟨full_term_at_some X j i Hs Hj.2, Hm j Hj.2⟩

/-! ### Acknowledgements, justified

`ackAgree γ b es t i`: the log `(b, es)` reaches `i` and has, at `i`, the term some log of
the leader of `t` has there. `ownLogGhost` keeps it of every acknowledgement a
non-leader has made in its current term above its commit index (`acksOk`): that is what
`heartbeat_commit_le_last` needs, and what a later `app`/`snap` of the same term cannot
undo -- they come from the same leader, so they agree with the log at and below `i`
(`ackAgree_term`). -/

def ackAgree (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry) (t i : w64) :
    IProp GF :=
  iprop(⌜uint.Z i ≤ plogLastIndexZ b es⌝ ∗
    ∃ ldr bL l, leadPrefix γ ldr t bL l ∗
      ⌜(plogTermAt bL l i).isSome ∧ plogTermAt bL l i = plogTermAt b es i⌝ ∗
      ∃ fp, lpfull γ ldr t bL l fp)

instance ackAgree_persistent (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry)
    (t i : w64) : Persistent (ackAgree (GF := GF) γ b es t i) := by
  unfold ackAgree; infer_instance
instance ackAgree_timeless (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry)
    (t i : w64) : Timeless (ackAgree (GF := GF) γ b es t i) := by
  unfold ackAgree; infer_instance

/-- A log that agrees with the leader of `t` at `i` agrees, at and below `i`, with every
other log of that leader. -/
theorem ackAgree_term (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry)
    (t i ldr' : w64) (bL : entryID) (l' : List raftpb.Entry) (j : w64) :
    PlogWfR b es →
    uint.Z b.index' ≤ uint.Z j → uint.Z bL.index' ≤ uint.Z j →
    uint.Z j ≤ uint.Z i →
    (plogTermAt bL l' j).isSome →
    ⊢ logRecs (GF := GF) γ b es -∗ ackAgree γ b es t i -∗ leadPrefix γ ldr' t bL l' -∗
      ⌜plogTermAt b es j = plogTermAt bL l' j⌝ := by
  intro Hwf Hj1 Hj2 Hji Hs'
  unfold ackAgree
  iintro #Hr ⟨%Hi, %ldr, %bL0, %l, #Hp, %HsEq, -⟩ #Hp'
  obtain ⟨Hs, Heq⟩ := HsEq
  icases leadPrefix_base γ ldr ldr' t bL0 bL l l' $$ Hp Hp' with %Hb
  subst Hb
  ihave ⟨%Hwfl, #Hrl⟩ := leadPrefix_wf γ ldr t _ l $$ Hp
  icases logRecs_agree γ b es _ l $$ Hr Hrl with %HRA
  have Hsi : (plogTermAt b es i).isSome := by rw [← Heq]; exact Hs
  have Hj := plog_match_down b es _ l i Hwf Hwfl HRA Hsi Heq.symm j Hj1 Hj2 Hji
  have Hsl : (plogTermAt bL0 l j).isSome := by
    obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
    apply plogTermAt_in_range
    have := plogTermAt_some_range _ _ _ _ Hx
    omega
  icases leadPrefix_agree γ ldr ldr' t _ l l' j Hsl Hs' $$ Hp Hp' with %Hj'
  ipureintro; rw [Hj, Hj']

end ghost

end EtcdGrove
end Perennial
