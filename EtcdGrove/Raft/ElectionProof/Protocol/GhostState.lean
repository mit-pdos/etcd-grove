/-
Port of election_proof/protocol.v, lines 2494–3198 at feb5c73d4: messages, a node's
protocol state `ownRaftGhost`, the history invariants, the commit invariant, the
proposal registry, and the pure facts about the vote tally. (On top of
`Protocol/Ghost.lean`; the log ghost state across a step is `Protocol/StepGhost.lean`.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker. Persistent/Timeless instances are proved.
* Names as in `Protocol/Ghost.lean`: `is_message` → `isMessage`, `own_log_ghost` →
  `ownLogGhost`, `own_raft_ghost` → `ownRaftGhost`, `raft_commit_inv` →
  `raftCommitInv`; Prop-valued `vote_hist_ok` → `VoteHistOk`, `terms_ok` → `TermsOk`,
  `log_ok` → `LogOk`, `role_ok` → `RoleOk`, ...; `msg_free` (a `bool`) is `MsgFree`
  (the name `Model.lean` uses). Rocq's `Notation term_rec`/`prop_rec` are the
  `abbrev`s `TermRec`/`PropRec`, left-nested as in Rocq (`((γt, b), l0)`,
  `((γq, γk), e0)`), so `.1.1`/`.1.2`/`.2` read as in Rocq. The vote-time log data
  `(T, d, F)` is `((T, d), F) : (w64 × Bool) × List raftpb.Entry` for the same reason.
* `DfracDiscarded` is `DFrac.discard`; the half `1/2` is `(1 : Qp).half`.
* Rocq's section has `invGS Σ` throughout; here `[InvGS GF]` is a section variable only
  from `raftCommitInv` on (the definitions before it do not use invariants, and an
  unused instance binder would be one more thing for their users to supply).
* `pbecome_follower_vote_ne`/`_same`, `vote_hist_ok_eq` are Rocq `Local`; they are
  public here (later modules use them).
* `vote_hist_fresh`, `ev_pair`, `elem_of_granted*` keep their Rocq (snake_case) names
  (they do not start with a definition's name).
-/
import EtcdGrove.Raft.ElectionProof.Protocol.Ghost

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF]

/-! ### Messages -/

def isMessage (γ : RaftElectionNames) (m : Msg) : IProp GF :=
  match m.ty with
  | .vote =>
      -- the candidate's campaign record, whose last entry the request reports
      -- (2026-10-03)
      iprop(∃ Fc, isCamp γ m.src m.term Fc ∗
        ⌜plogLast base0 Fc = entryID.mk m.logterm m.index⌝)
  | .voteResp =>
      if m.reject then iprop(True)
      else isVote γ m.src m.term m.dst
  | .app =>
      iprop(⌜AppPayloadOk m⌝ ∗
      isLeader γ m.src m.term ∗
      -- the leader's log `l` has `(logterm, index)` and the entries after; its full
      -- log agrees with a committed log at `Commit`
      (∃ bL l fp, leadPrefix γ m.src m.term bL l ∗
         ⌜plogTermAt bL l m.index = some m.logterm ∧
           m.entries <+: plogFrom bL l (m.index + W64 1)⌝ ∗
         lpfull γ m.src m.term bL l fp ∗
         commitIn γ (fp ++ l) m.commit m.term ∗
         -- the leader's committed prefix up to `Commit` (2026-10-05)
         isCommitted γ ((fp ++ l).take (uint.Z m.commit).toNat)) ∗
      ⌜m.src ≠ W64 0⌝)
  | .appResp =>
      if m.reject then iprop(True)
      else isAcked γ m.src m.term m.index
  | .heartbeat =>
      iprop(isLeader γ m.src m.term ∗
      (∃ Fl, leadFull γ m.term Fl ∗ commitIn γ Fl m.commit m.term ∗
         isCommitted γ (Fl.take (uint.Z m.commit).toNat)) ∗
      -- `Commit ≤ pr.Match`, which the receiver acknowledged
      (∃ i, ⌜uint.Z m.commit ≤ uint.Z i⌝ ∗ isAcked γ m.dst m.term i) ∗
      ⌜m.src ≠ W64 0⌝)
  | .snap =>
      -- the leader's, of a committed prefix ending in a real entry
      iprop(isLeader γ m.src m.term ∗
      isSnapMeta γ m.logterm m.index ∗
      -- the leader's log has the snapshot's last entry
      (∃ bL l fp, leadPrefix γ m.src m.term bL l ∗
         ⌜plogTermAt bL l m.index = some m.logterm⌝ ∗
         lpfull γ m.src m.term bL l fp ∗
         commitIn γ (fp ++ l) m.index m.term ∗
         -- the committed prefix the snapshot covers (2026-10-05)
         isCommitted γ ((fp ++ l).take (uint.Z m.index).toNat)) ∗
      ⌜m.src ≠ W64 0⌝)
  | _ => iprop(True)

instance isMessage_persistent (γ : RaftElectionNames) (m : Msg) :
    Persistent (isMessage (GF := GF) γ m) := by
  unfold isMessage; split <;> (try split) <;> infer_instance

instance isMessage_timeless (γ : RaftElectionNames) (m : Msg) :
    Timeless (isMessage (GF := GF) γ m) := by
  unfold isMessage; split <;> (try split) <;> infer_instance

/-- The message types that carry nothing. -/
def MsgFree (ty : MsgType) : Bool :=
  match ty with
  | .heartbeatResp | .propose | .preVote
  | .preVoteResp | .readIndex | .readIndexResp => true
  | _ => false

theorem isMessage_free (γ : RaftElectionNames) (m : Msg) :
    MsgFree m.ty = true → ⊢ isMessage (GF := GF) γ m := by
  intro Hty
  unfold isMessage
  cases h : m.ty <;> simp only [h, MsgFree] at Hty ⊢ <;>
    first | exact absurd Hty (by decide) | exact true_intro

/-- A *rejecting* `voteResp` is free too: it reports no vote. -/
theorem isMessage_reject (γ : RaftElectionNames) (src dst term : w64) :
    ⊢ isMessage (GF := GF) γ (Msg.plain .voteResp src dst term true) := by
  unfold isMessage Msg.plain; exact true_intro

/-- A granting `voteResp` carries the vote it reports, and nothing else. -/
theorem isMessage_grant (γ : RaftElectionNames) (src dst term : w64) :
    isVote (GF := GF) γ src term dst ⊢ isMessage γ (Msg.plain .voteResp src dst term false) := by
  unfold isMessage Msg.plain; exact .rfl

theorem isMessage_grant_inv (γ : RaftElectionNames) (m : Msg) :
    m.ty = .voteResp →
    m.reject = false →
    ⊢ isMessage (GF := GF) γ m -∗ isVote γ m.src m.term m.dst := by
  intro Hty Hrej
  unfold isMessage; rw [Hty]; simp only [Hrej, Bool.false_eq_true, ↓reduceIte]
  iintro H; iexact H

/-! ### A node's protocol state -/

def VoteHistOk (voted : GMap w64 w64) (s : PState) : Prop :=
  (∀ t, (voted !! t).isSome → uint.Z t ≤ uint.Z s.term) ∧
  voted !! s.term = (if s.vote = W64 0 then none else some s.vote)

/-- `pbecomeFollower` keeps the vote only when the term does not move. -/
theorem pbecomeFollower_vote_ne (s : PState) (term lead : w64) :
    term ≠ s.term → (pbecomeFollower s term lead).vote = W64 0 := by
  intro Hne; simp [pbecomeFollower, Hne]

theorem pbecomeFollower_vote_same (s : PState) (lead : w64) :
    (pbecomeFollower s s.term lead).vote = s.vote := by
  simp [pbecomeFollower]

/-- A term the node has not reached yet is free to vote in. -/
theorem vote_hist_fresh (voted : GMap w64 w64) (s : PState) (t : w64) :
    VoteHistOk voted s →
    uint.Z s.term < uint.Z t →
    voted !! t = none := by
  intro H Hlt
  cases h : voted !! t with
  | none => rfl
  | some c =>
    have := H.1 t (by simp [h])
    omega

/-- `VoteHistOk` reads only `term` and `vote`. -/
theorem VoteHistOk_eq (voted : GMap w64 w64) (s1 s2 : PState) :
    VoteHistOk voted s1 →
    s2.term = s1.term →
    s2.vote = s1.vote →
    VoteHistOk voted s2 := by
  intro H Ht Hv; unfold VoteHistOk at *; rw [Ht, Hv]; exact H

def leaderWit (γ : RaftElectionNames) (id : w64) (s : PState) : IProp GF :=
  match s.role with
  | .leader => isLeader γ id s.term
  | _ => iprop(True)

instance leaderWit_persistent (γ : RaftElectionNames) (id : w64) (s : PState) :
    Persistent (leaderWit (GF := GF) γ id s) := by
  unfold leaderWit; split <;> infer_instance

instance leaderWit_timeless (γ : RaftElectionNames) (id : w64) (s : PState) :
    Timeless (leaderWit (GF := GF) γ id s) := by
  unfold leaderWit; split <;> infer_instance

/-- The terms a node has allocated a term log for: ones it has left behind, or the
current one if it is leader in it. -/
/- What a node's term map holds: `isTermLog`'s triple. -/
abbrev TermRec := (GName × entryID) × List raftpb.Entry

def TermsOk (terms : GMap w64 TermRec) (s : PState) : Prop :=
  ∀ t, (terms !! t).isSome →
    uint.Z t < uint.Z s.term ∨
    (t = s.term ∧ s.role = .leader)

/-- A leader owns the term log of its term, whose recorded base and initial log are the
leader's base and a prefix of its log, and holds a fragment of it for every entry it has
created since (`leadFrags`). -/
def leadLogOwn (γ : RaftElectionNames) (s : PState) (terms : GMap w64 TermRec) : IProp GF :=
  match s.role with
  | .leader =>
      iprop(∃ γt, ∃ (M : GMap w64 (raftpb.Entry × w64)), ∃ l0,
        ⌜terms !! s.term = some ((γt, s.base), l0)⌝ ∗
        ghostMapAuth γt 1 M ∗
        ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ∗
        -- nothing in the term log is past the leader's last index: what makes
        -- `Step.propose`'s new indices fresh
        ⌜∀ i, (M !! i).isSome → uint.Z i ≤ plogLastIndexZ s.base s.log⌝ ∗
        ⌜l0 <+: s.log⌝ ∗
        leadFrags γt l0 s.log)
  | _ => iprop(True)

instance leadLogOwn_timeless (γ : RaftElectionNames) (s : PState) (terms : GMap w64 TermRec) :
    Timeless (leadLogOwn (GF := GF) γ s terms) := by
  unfold leadLogOwn; split <;> infer_instance

/-- A leader's `Match` values are backed by acknowledgements. -/
def matchedOk (γ : RaftElectionNames) (s : PState) : IProp GF :=
  match s.role with
  | .leader => iprop([∗map] v ↦ i ∈ s.matched, isAcked γ v s.term i)
  | _ => iprop(True)

instance matchedOk_persistent (γ : RaftElectionNames) (s : PState) :
    Persistent (matchedOk (GF := GF) γ s) := by
  unfold matchedOk; split <;> infer_instance
instance matchedOk_timeless (γ : RaftElectionNames) (s : PState) :
    Timeless (matchedOk (GF := GF) γ s) := by
  unfold matchedOk; split <;> infer_instance

/-- The log's shape: well-formed (in range), and `base ≤ commit ≤ lastIndex()`. -/
def LogOk (s : PState) : Prop :=
  PlogWfR s.base s.log ∧
  uint.Z s.base.index' ≤ uint.Z s.commit ∧
  uint.Z s.commit ≤ plogLastIndexZ s.base s.log

/-- A node acknowledges only at its own term. -/
def AcksTerm (s : PState) (acks : GMap (w64 × w64) Unit) : Prop :=
  ∀ k, (acks !! k).isSome → uint.Z k.1 ≤ uint.Z s.term

/-- An acknowledgement of the current term above the commit index is justified by the
log (`ackAgree`). Only of a non-leader: a leader's log does not shrink, and it leaves its
term only for a higher one. -/
def ackOk (γ : RaftElectionNames) (s : PState) (k : w64 × w64) : IProp GF :=
  iprop(∀ (_ : k.1 = s.term ∧ uint.Z s.commit < uint.Z k.2),
    ackAgree γ s.base s.log k.1 k.2)

instance ackOk_persistent (γ : RaftElectionNames) (s : PState) (k : w64 × w64) :
    Persistent (ackOk (GF := GF) γ s k) := by
  unfold ackOk; infer_instance
instance ackOk_timeless (γ : RaftElectionNames) (s : PState) (k : w64 × w64) :
    Timeless (ackOk (GF := GF) γ s k) := by
  unfold ackOk; infer_instance

def acksOk (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit) : IProp GF :=
  match s.role with
  | .leader => iprop(True)
  | _ => iprop([∗map] k ↦ _u ∈ acks, ackOk γ s k)

instance acksOk_persistent (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    Persistent (acksOk (GF := GF) γ s acks) := by
  unfold acksOk; split <;> infer_instance
instance acksOk_timeless (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    Timeless (acksOk (GF := GF) γ s acks) := by
  unfold acksOk; split <;> infer_instance

/-! ### The history invariants (2026-10-03, bound reworked 2026-10-05)

`bnd s kl`: the terms whose leaders a node's histories (`hist`) may mention -- those
below its term, and its term itself once the node knows that term's leader,
`kl = some ldr` (or is it). `kl` is ghost (`ownRaftGhost` quantifies it): it is set
when a message of the leader of the term arrives or the node wins, kept within the term
-- also when the node forgets its leader (`Step.abandon`, pre-vote) -- and reset on a new
term. So `bnd` never decreases. `klOk` says that the known leader won, and, while the
node has not voted in the term, without its vote: a first vote cast after learning the
leader then records that it did not count in the election (`voteJust`). -/
def bnd (s : PState) (kl : Option w64) : Int :=
  match kl with
  | some _ => uint.Z s.term + 1
  | none => uint.Z s.term

def klOk (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) : IProp GF :=
  match kl with
  | none => iprop(⌜s.role ≠ .leader⌝)
  | some ldr => iprop((∃ q, isWin γ ldr s.term q ∗ ⌜s.vote = W64 0 → id ∉ q⌝) ∗
                ⌜s.role = .leader → ldr = id⌝)

instance klOk_persistent (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    Persistent (klOk (GF := GF) γ id s kl) := by
  unfold klOk; split <;> infer_instance
instance klOk_timeless (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    Timeless (klOk (GF := GF) γ id s kl) := by
  unfold klOk; split <;> infer_instance

/-- No term in a node's full log is above its own; a candidate has none of its own term
either. -/
def TermsLe (s : PState) (F : List raftpb.Entry) : Prop :=
  ∀ (j x : w64), plogTermAt base0 F j = some x →
    uint.Z x ≤ uint.Z s.term ∧
    (s.role = .candidate → uint.Z x < uint.Z s.term)

/-- A candidate's full log is its campaign record; a leader's extends it, by at least the
leader's entry, and ends in an entry of its term. -/
def campOwn (γ : RaftElectionNames) (id : w64) (s : PState) (F : List raftpb.Entry) : IProp GF :=
  match s.role with
  | .candidate => isCamp γ id s.term F
  | .leader => iprop(∃ F0, isCamp γ id s.term F0 ∗
       ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
         (plogLast base0 F).term' = s.term⌝)
  | .follower => iprop(True)

instance campOwn_persistent (γ : RaftElectionNames) (id : w64) (s : PState)
    (F : List raftpb.Entry) : Persistent (campOwn (GF := GF) γ id s F) := by
  unfold campOwn; split <;> infer_instance
instance campOwn_timeless (γ : RaftElectionNames) (id : w64) (s : PState)
    (F : List raftpb.Entry) : Timeless (campOwn (GF := GF) γ id s F) := by
  unfold campOwn; split <;> infer_instance

/-- Node `v`'s `k`-th vote-time log: it voted in `T` with full log `F`, knowing the leader
of `T` iff `d` (so its histories then are bounded by `vbnd T d`). -/
def vbnd (T : w64) (d : Bool) : Int := uint.Z T + (if d then 1 else 0)

def isVlog (γ : RaftElectionNames) (v : w64) (k : Nat) (T : w64) (d : Bool)
    (F : List raftpb.Entry) : IProp GF :=
  iprop(∃ γl, ⌜γ.reVlogs !! v = some γl⌝ ∗
    k ↪[γl]□ (((T, d), F) : (w64 × Bool) × List raftpb.Entry))

instance isVlog_persistent (γ : RaftElectionNames) (v : w64) (k : Nat) (T : w64) (d : Bool)
    (F : List raftpb.Entry) : Persistent (isVlog (GF := GF) γ v k T d F) := by
  unfold isVlog; infer_instance
instance isVlog_timeless (γ : RaftElectionNames) (v : w64) (k : Nat) (T : w64) (d : Bool)
    (F : List raftpb.Entry) : Timeless (isVlog (GF := GF) γ v k T d F) := by
  unfold isVlog; infer_instance

/-- A vote-time log has the history of every acknowledgement of an earlier term (all of
them were made before the vote: a node acknowledges only at its own term). -/
def vlogsOk (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)) : IProp GF :=
  iprop([∗map] x ∈ vlogs, ⌜uint.Z x.1.1 ≤ uint.Z s.term⌝ ∗
    [∗map] k ↦ _u ∈ acks, ∀ (_ : uint.Z k.1 < uint.Z x.1.1),
      hist γ x.2 k.1 k.2 (vbnd x.1.1 x.1.2))

instance vlogsOk_persistent (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)) :
    Persistent (vlogsOk (GF := GF) γ s acks vlogs) := by
  unfold vlogsOk; infer_instance

def histsOk (γ : RaftElectionNames) (s : PState) (kl : Option w64) (F : List raftpb.Entry)
    (acks : GMap (w64 × w64) Unit) : IProp GF :=
  iprop([∗map] k ↦ _u ∈ acks, hist γ F k.1 k.2 (bnd s kl))

instance histsOk_persistent (γ : RaftElectionNames) (s : PState) (kl : Option w64)
    (F : List raftpb.Entry) (acks : GMap (w64 × w64) Unit) :
    Persistent (histsOk (GF := GF) γ s kl F acks) := by
  unfold histsOk; infer_instance

/-- What a vote of `v` for `c` in `T` records: `v`'s full log `Fv` then (`isVlog`), with
records, and that `c`'s campaign log was at least as up to date (`Step.grantVote`'s
premise); and, if `v` then knew the leader of `T` (`d`), that `v` is not in that leader's
winning quorum (2026-10-05). -/
/- `v`'s vote in `T`, with `d` and full log `F`, is the last event of a prefix of its
history, and `F` has the history (`hist`) of every acknowledgement of an earlier term
before it (2026-10-05). With `ackEv` this replaces the voter's own ghost maps in Leader
Completeness (`ev_pair`): an acknowledgement of an earlier term than the vote's is
before it in the history, which is in term order. -/
def voteEv (γ : RaftElectionNames) (v T : w64) (d : Bool) (F : List raftpb.Entry) : IProp GF :=
  iprop(∃ γe L0, ⌜γ.reEvs !! v = some γe⌝ ∗ monoListLbOwn γe (L0 ++ [Aev.vote T d F]) ∗
    ∀ (t i : w64), ∀ (_ : Aev.ack t i ∈ L0 ∧ uint.Z t < uint.Z T), hist γ F t i (vbnd T d))

instance voteEv_persistent (γ : RaftElectionNames) (v T : w64) (d : Bool)
    (F : List raftpb.Entry) : Persistent (voteEv (GF := GF) γ v T d F) := by
  unfold voteEv; infer_instance

/-- (Lean addition: Rocq's instance search unfolds `vote_ev` for `vote_just_timeless`.) -/
instance voteEv_timeless (γ : RaftElectionNames) (v T : w64) (d : Bool)
    (F : List raftpb.Entry) : Timeless (voteEv (GF := GF) γ v T d F) := by
  unfold voteEv; infer_instance

theorem ev_pair (γ : RaftElectionNames) (v t i T : w64) (d : Bool) (F : List raftpb.Entry) :
    uint.Z t < uint.Z T →
    ⊢ ackEv (GF := GF) γ v t i -∗ voteEv γ v T d F -∗ hist γ F t i (vbnd T d) := by
  -- PORT: proof
  sorry

def voteJust (γ : RaftElectionNames) (v T c : w64) : IProp GF :=
  iprop(∃ k d Fv Fc, isVlog γ v k T d Fv ∗ isCamp γ c T Fc ∗ logRecs γ base0 Fv ∗
    ⌜PlogWf base0 Fv ∧ plogUpToDate base0 Fv (plogLast base0 Fc) = true⌝ ∗
    (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) ∗
    voteEv γ v T d Fv)

instance voteJust_persistent (γ : RaftElectionNames) (v T c : w64) :
    Persistent (voteJust (GF := GF) γ v T c) := by
  have : ∀ d : Bool, Persistent (PROP := IProp GF)
      (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) :=
    fun _ => inferInstance
  unfold voteJust; infer_instance
instance voteJust_timeless (γ : RaftElectionNames) (v T c : w64) :
    Timeless (voteJust (GF := GF) γ v T c) := by
  have : ∀ d : Bool, Timeless (PROP := IProp GF)
      (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) :=
    fun _ => inferInstance
  unfold voteJust; infer_instance

/-- A node's event history, authoritative: in term order, at or below its term, and every
acknowledgement in it is in its acknowledgement map. -/
def ownEvs (γ : RaftElectionNames) (id T : w64) (acks : GMap (w64 × w64) Unit) : IProp GF :=
  iprop(∃ γe evs, ⌜γ.reEvs !! id = some γe⌝ ∗ monoListAuthOwn γe 1 evs ∗
    ⌜EvSorted evs ∧ (∀ e, e ∈ evs → uint.Z (aevTerm e) ≤ uint.Z T) ∧
      (∀ t i, Aev.ack t i ∈ evs → (acks !! (t, i)).isSome)⌝)

instance ownEvs_timeless (γ : RaftElectionNames) (id T : w64) (acks : GMap (w64 × w64) Unit) :
    Timeless (ownEvs (GF := GF) γ id T acks) := by
  unfold ownEvs; infer_instance

theorem ownEvs_mono (γ : RaftElectionNames) (id T T' : w64) (acks acks' : GMap (w64 × w64) Unit) :
    uint.Z T ≤ uint.Z T' → (∀ k, (acks !! k).isSome → (acks' !! k).isSome) →
    ⊢ ownEvs (GF := GF) γ id T acks -∗ ownEvs γ id T' acks' := by
  -- PORT: proof
  sorry

theorem ownEvs_ack (γ : RaftElectionNames) (id T : w64) (acks : GMap (w64 × w64) Unit) (i : w64) :
    ⊢ ownEvs (GF := GF) γ id T acks ==∗ ownEvs γ id T (<[(T, i) := ()]> acks) ∗ ackEv γ id T i := by
  -- PORT: proof
  sorry

theorem ownEvs_vote (γ : RaftElectionNames) (id T T' : w64) (acks : GMap (w64 × w64) Unit)
    (d : Bool) (F : List raftpb.Entry) :
    uint.Z T ≤ uint.Z T' →
    ⊢ ownEvs (GF := GF) γ id T acks -∗
      ([∗map] k ↦ _u ∈ acks, ∀ (_ : uint.Z k.1 < uint.Z T'), hist γ F k.1 k.2 (vbnd T' d)) ==∗
      ownEvs γ id T' acks ∗ voteEv γ id T' d F := by
  -- PORT: proof
  sorry

/-! ### The commit invariant (2026-10-05)

`votesTbl γ`: half of every node's vote map, with the justification of each vote
(`voteJust`) -- the other half is the node's (`ownRaftGhost`). What Leader Completeness
needs of the voter in both quorums, without that voter's ghost state (`tbl_voter`): its
vote record. (Its acknowledgement's history comes from `ackEv`/`voteEv`.) This is why
the safety theorems no longer need the whole cluster.

`committedJust γ l`: what justifies the global committed log `l` -- empty, or the first
`n` entries of a full log `G` of the leader of a term `t`, whose entry at `n` is of `t`
and which a quorum acknowledged up to `n` (`cq`: `leadFull` -- the leader's `isWin`, its
`leadPrefix` and its full log -- and the quorum of `isAcked`).

`raftCommitInv γ`: the authority of the global committed log, with its justification,
and the vote table. -/

def votesTbl (γ : RaftElectionNames) : IProp GF :=
  iprop([∗map] v ↦ γv ∈ γ.reVotes, ∃ voted : GMap w64 w64,
    ghostMapAuth γv (1 : Qp).half voted ∗ [∗map] T ↦ c ∈ voted, voteJust γ v T c)

instance votesTbl_timeless (γ : RaftElectionNames) : Timeless (votesTbl (GF := GF) γ) := by
  unfold votesTbl; infer_instance

theorem votesTbl_just (γ : RaftElectionNames) (v T c : w64) :
    ⊢ votesTbl (GF := GF) γ -∗ isVote γ v T c -∗ voteJust γ v T c := by
  -- PORT: proof
  sorry

theorem votesTbl_insert (γ : RaftElectionNames) (id : w64) (γv : GName) (voted : GMap w64 w64)
    (T c : w64) :
    γ.reVotes !! id = some γv → voted !! T = none →
    ⊢ voteJust (GF := GF) γ id T c -∗ votesTbl γ -∗ ghostMapAuth γv (1 : Qp).half voted ==∗
      votesTbl γ ∗ ghostMapAuth γv (1 : Qp).half (<[T := c]> voted) ∗ T ↪[γv]□ c := by
  -- PORT: proof
  sorry

def committedJust (γ : RaftElectionNames) (l : List raftpb.Entry) : IProp GF :=
  iprop(⌜l = []⌝ ∨ ∃ t n G, cq γ t n G ∗ ⌜l = G.take (uint.Z n).toNat⌝)

instance committedJust_timeless (γ : RaftElectionNames) (l : List raftpb.Entry) :
    Timeless (committedJust (GF := GF) γ l) := by
  unfold committedJust; infer_instance

def raftN : Namespace := nroot .@ "raft_commit"

/-! ### The proposal registry (2026-10-05)

`propAu γ e0 Q`: the client's update for a proposal of the unstamped entry `e0`, run
**when the entry is committed** -- when the global log `l` is extended to `l ++ [e]`,
`e = stampAt e0 t i` the entry at index `i = length l + 1`. It is handed the authority
of the global log just extended and must give it back unchanged; it produces `Q t i`
(the client learns where its entry landed).

It is a plain wand, not a fancy update: it is stored in `raftCommitInv`, so it is under
a later when `Step.commit` runs it, and a ghost step has no later to spend (no physical
step, no credits); a wand under a later still produces its result under a later, which
is where the registry keeps it. A client that wants a fancy update takes
`Q := fun t i => |={⊤ \ ↑raftN}=> Q' t i` and runs it when it collects.

A registered proposal `(t, i) ↦ (γq, γk, e0)` has the leader's entry `stampAt e0 t i`
(`propsIdx`, which keeps registration fresh: the leader of `t` is creating index `i`
now) and is in one of three states (`propSlot`): pending, holding the update, while the
global log has no entry of term `t` at `i`; done, holding its result `Φ (t, i)`, once it
has; collected, holding the token the client traded for the result (`prop_collect`).
The client's `Q` is tied to the slot's `Φ` by a saved predicate (`isProp`). -/

def propAu (γ : RaftElectionNames) (e0 : raftpb.Entry) (Q : w64 → w64 → IProp GF) : IProp GF :=
  iprop(∀ (t i : w64) (l : List raftpb.Entry),
    ⌜(l.length : Int) + 1 = uint.Z i⌝ -∗
    ownCommitted γ (l ++ [stampAt e0 t i]) -∗
    ownCommitted γ (l ++ [stampAt e0 t i]) ∗ Q t i)

abbrev PropRec := (GName × GName) × raftpb.Entry

def propSlot (γ : RaftElectionNames) (k : w64 × w64) (v : PropRec) (l : List raftpb.Entry) :
    IProp GF :=
  iprop(∃ Φ : w64 × w64 → IProp GF, savedPredOwn v.1.1 DFrac.discard Φ ∗
    ( (⌜∀ e, l[pos k.2]? = some e → e.Term' ≠ k.1⌝ ∗
        propAu γ v.2 (fun t i => Φ (t, i)))
    ∨ (⌜∃ e, l[pos k.2]? = some e ∧ e.Term' = k.1⌝ ∗ Φ k)
    ∨ token v.1.2 ))

def propsIdx (γ : RaftElectionNames) (R : GMap (w64 × w64) PropRec) : IProp GF :=
  iprop([∗map] k ↦ v ∈ R, isEntry γ (stampAt v.2 k.1 k.2) ∗ ⌜0 < uint.Z k.2⌝)

instance propsIdx_persistent (γ : RaftElectionNames) (R : GMap (w64 × w64) PropRec) :
    Persistent (propsIdx (GF := GF) γ R) := by
  unfold propsIdx; infer_instance
instance propsIdx_timeless (γ : RaftElectionNames) (R : GMap (w64 × w64) PropRec) :
    Timeless (propsIdx (GF := GF) γ R) := by
  unfold propsIdx; infer_instance

/-- The client's handle on its proposal: registered at `(t, i)`, with result `Q`; and the
token it trades for `Q t i`. -/
def isProp (γ : RaftElectionNames) (t i : w64) (γp : GName × GName) (Q : w64 → w64 → IProp GF) :
    IProp GF :=
  iprop(∃ e0 : raftpb.Entry, (t, i) ↪[γ.reProps]□ (((γp.1, γp.2), e0) : PropRec) ∗
        savedPredOwn γp.1 DFrac.discard (fun ti : w64 × w64 => Q ti.1 ti.2))

def propTok (γp : GName × GName) : IProp GF := token γp.2

instance isProp_persistent (γ : RaftElectionNames) (t i : w64) (γp : GName × GName)
    (Q : w64 → w64 → IProp GF) : Persistent (isProp γ t i γp Q) := by
  unfold isProp; infer_instance
instance propTok_timeless (γp : GName × GName) : Timeless (propTok (GF := GF) γp) := by
  unfold propTok; infer_instance

section inv
variable [InvGS GF]

def raftCommitInv (γ : RaftElectionNames) : IProp GF :=
  inv raftN iprop(∃ l, ∃ (R : GMap (w64 × w64) PropRec),
               ownCommitted γ l ∗ committedJust γ l ∗ votesTbl γ ∗
               ghostMapAuth γ.reProps 1 R ∗ propsIdx γ R ∗
               [∗map] k ↦ v ∈ R, propSlot γ k v l)

instance raftCommitInv_persistent (γ : RaftElectionNames) :
    Persistent (raftCommitInv (GF := GF) γ) := by
  unfold raftCommitInv; infer_instance

/-- A node's committed prefix: the first `commit` entries of its full log `fp ++ log` (the
entries at indices `1 .. commit`). -/
def cprefix (fp : List raftpb.Entry) (s : PState) : List raftpb.Entry :=
  (fp ++ s.log).take (uint.Z s.commit).toNat

/-- The terms a node has won: as `TermsOk`. -/
def WinsOk (wins : GMap w64 (GSet w64)) (s : PState) : Prop :=
  ∀ t, (wins !! t).isSome →
    uint.Z t < uint.Z s.term ∨
    (t = s.term ∧ s.role = .leader)

def ownLogGhost (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) : IProp GF :=
  iprop(∃ γm, ∃ (terms : GMap w64 TermRec), ∃ γa, ∃ (acks : GMap (w64 × w64) Unit),
    ∃ (fp : List raftpb.Entry), ∃ γc, ∃ (camps : GMap w64 (List raftpb.Entry)), ∃ γl,
    ∃ (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)), ∃ γw,
    ∃ (wins : GMap w64 (GSet w64)),
    "%Htname"  ∷ ⌜γ.reTerms !! id = some γm⌝ ∗
    "Hterms"   ∷ ghostMapAuth γm 1 terms ∗
    "#Htfrags" ∷ ([∗map] t ↦ γt ∈ terms, t ↪[γm]□ γt) ∗
    "%Hterms_ok" ∷ ⌜TermsOk terms s⌝ ∗
    "Htlog"    ∷ leadLogOwn γ s terms ∗
    "%Haname"  ∷ ⌜γ.reAcks !! id = some γa⌝ ∗
    "Hacks"    ∷ ghostMapAuth γa 1 acks ∗
    "#Hafrags" ∷ ([∗map] k ↦ u ∈ acks, k ↪[γa]□ u) ∗
    "%Hacks_term" ∷ ⌜AcksTerm s acks⌝ ∗
    "#Hacks_ok" ∷ acksOk γ s acks ∗
    "%Hlog_ok" ∷ ⌜LogOk s⌝ ∗
    "#Hrecs"   ∷ logRecs γ s.base s.log ∗
    "#Hmatched" ∷ matchedOk γ s ∗
    "#Hcommit" ∷ commitIn γ (fp ++ s.log) s.commit s.term ∗
    "#Hbase"   ∷ baseOk γ s.base ∗
    -- 2026-10-03: the full log, campaign records, vote-time logs and the histories of
    -- acknowledgements
    "%Hfull"   ∷ ⌜FullOk s.base fp ∧ PlogWf s.base s.log ∧
                   TermsLe s (fp ++ s.log)⌝ ∗
    "#Hfrecs"  ∷ logRecs γ base0 fp ∗
    "%Hcname"  ∷ ⌜γ.reCamp !! id = some γc⌝ ∗
    "Hcamps"   ∷ ghostMapAuth γc 1 camps ∗
    "%Hcamps_ok" ∷ ⌜∀ T, (camps !! T).isSome → uint.Z T ≤ uint.Z s.term⌝ ∗
    "#Hcown"   ∷ campOwn γ id s (fp ++ s.log) ∗
    "%Hlname"  ∷ ⌜γ.reVlogs !! id = some γl⌝ ∗
    "Hvlogs"   ∷ ghostMapAuth γl 1 vlogs ∗
    "#Hvlogs_ok" ∷ vlogsOk γ s acks vlogs ∗
    "#Hhists"  ∷ histsOk γ s kl (fp ++ s.log) acks ∗
    -- 2026-10-05: winning quorums and the known leader
    "%Hwname"  ∷ ⌜γ.reWins !! id = some γw⌝ ∗
    "Hwins"    ∷ ghostMapAuth γw 1 wins ∗
    "%Hwins_ok" ∷ ⌜WinsOk wins s⌝ ∗
    "#Hkl"     ∷ klOk γ id s kl ∗
    -- 2026-10-05: the event history, the commit invariant, and the committed prefix as
    -- entries, a prefix of the global log
    "Hevs"     ∷ ownEvs γ id s.term acks ∗
    "#Hinv"    ∷ raftCommitInv γ ∗
    "#Hcmt"    ∷ isCommitted γ (cprefix fp s))

-- Not `Timeless` since 2026-10-05: it holds the invariant `raftCommitInv`.

/-- A role other than follower has voted for itself; a candidate has no leader.
(Invariants of every reachable state, 2026-10-03; used for the self-vote of a candidate
and in `Step.win`.) -/
def RoleOk (id : w64) (s : PState) : Prop :=
  (s.role ≠ .follower → s.vote = id) ∧
  (s.role = .candidate → s.lead = W64 0)

def ownRaftGhost (γ : RaftElectionNames) (id : w64) (s : PState) : IProp GF :=
  iprop(∃ γv, ∃ (voted : GMap w64 w64), ∃ (kl : Option w64),
    "%Hname"  ∷ ⌜γ.reVotes !! id = some γv⌝ ∗
    "%Hidnz"  ∷ ⌜id ≠ W64 0⌝ ∗
    "Hvoted"  ∷ ghostMapAuth γv (1 : Qp).half voted ∗
    "%Hhist"  ∷ ⌜VoteHistOk voted s⌝ ∗
    "#Hfrags" ∷ ([∗map] t ↦ c ∈ voted, isVote γ id t c) ∗
    "#Hout"   ∷ ([∗list] m ∈ s.outbox, isMessage γ m) ∗
    "#Htally" ∷ ([∗map] v ↦ _u ∈ toMap (granted s.votes), isVote γ v s.term id) ∗
    "#Hlead"  ∷ leaderWit γ id s ∗
    "Hlg"     ∷ ownLogGhost γ id s kl ∗
    "%Hlead_ok" ∷ ⌜LeadOk id s⌝ ∗
    "%Hfollower_votes" ∷ ⌜FollowerVotesOk s⌝ ∗
    "#Hvrecs" ∷ ([∗map] t ↦ c ∈ voted, voteJust γ id t c) ∗
    "%Hrole_ok" ∷ ⌜RoleOk id s⌝)

-- Not `Timeless` since 2026-10-05: `ownLogGhost` holds the invariant `raftCommitInv`.

theorem ownRaftGhost_intro (γ : RaftElectionNames) (id : w64) (s : PState) (γv : GName)
    (voted : GMap w64 w64) (kl : Option w64) :
    γ.reVotes !! id = some γv →
    id ≠ W64 0 →
    ⊢ ghostMapAuth (GF := GF) γv (1 : Qp).half voted -∗
      ⌜VoteHistOk voted s⌝ -∗
      ([∗map] t ↦ c ∈ voted, isVote γ id t c) -∗
      ([∗list] m ∈ s.outbox, isMessage γ m) -∗
      ([∗map] v ↦ _u ∈ toMap (granted s.votes), isVote γ v s.term id) -∗
      leaderWit γ id s -∗
      ownLogGhost γ id s kl -∗
      ⌜LeadOk id s⌝ -∗
      ⌜FollowerVotesOk s⌝ -∗
      ([∗map] t ↦ c ∈ voted, voteJust γ id t c) -∗
      ⌜RoleOk id s⌝ -∗
      ownRaftGhost γ id s := by
  intro Hname Hidnz
  unfold ownRaftGhost
  iintro H1 %H2 #H3 #H4 #H5 #H6 H7 %H8 %H9 #H10 %H11
  iexists γv, voted, kl
  isplitr; · ipureintro; exact Hname
  isplitr; · ipureintro; exact Hidnz
  isplitl [H1]; · iexact H1
  isplitr; · ipureintro; exact H2
  isplitr; · iexact H3
  isplitr; · iexact H4
  isplitr; · iexact H5
  isplitr; · iexact H6
  isplitl [H7]; · iexact H7
  isplitr; · ipureintro; exact H8
  isplitr; · ipureintro; exact H9
  isplitr; · iexact H10
  ipureintro; exact H11

/-- A non-leader does not record itself as leader. -/
theorem ownRaftGhost_lead_ok (γ : RaftElectionNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜LeadOk id s⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hlead_ok

/-- A follower's tally is empty. -/
theorem ownRaftGhost_follower_votes (γ : RaftElectionNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜FollowerVotesOk s⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hfollower_votes

theorem matchedOk_eq (γ : RaftElectionNames) (s1 s2 : PState) :
    s2.role = s1.role →
    s2.term = s1.term →
    s2.matched = s1.matched →
    ⊢ matchedOk (GF := GF) γ s1 -∗ matchedOk γ s2 := by
  intro H1 H2 H3
  unfold matchedOk; rw [H1, H2, H3]
  iintro H; iexact H

theorem ownRaftGhost_excl (γ : RaftElectionNames) (id : w64) (s1 s2 : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s1 -∗ ownRaftGhost γ id s2 -∗ False := by
  -- the vote map is half the node's since 2026-10-05; the term-log map is whole
  -- PORT: proof
  sorry

/-- Everything in a node's outbox was legitimately put there. -/
theorem ownRaftGhost_outbox (γ : RaftElectionNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ([∗list] m ∈ s.outbox, isMessage γ m) := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iexact Hout

theorem ownRaftGhost_isLeader (γ : RaftElectionNames) (id : w64) (s : PState) :
    s.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ isLeader γ id s.term := by
  intro Hrole
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  unfold leaderWit; simp only [Hrole]
  iexact Hlead

end inv

/-! ### Pure facts about the vote tally -/

omit [FfiSyntax] in
theorem elem_of_granted (votes : GMap w64 Bool) (v : w64) :
    v ∈ granted votes ↔ votes !! v = some true := by
  unfold granted
  rw [GMap.elem_of_dom]
  constructor
  · rintro ⟨b, Hb⟩
    rw [GMap.mapLookup_filter_Some] at Hb
    obtain ⟨Hv, Hb⟩ := Hb
    cases b
    · exact absurd Hb (by decide)
    · exact Hv
  · intro Hv
    exact ⟨true, (GMap.mapLookup_filter_Some _ _ _ _).mpr ⟨Hv, rfl⟩⟩

omit [FfiSyntax] in
theorem granted_empty : granted ∅ = ∅ := by
  unfold granted; rw [GMap.map_filter_empty, GMap.dom_empty_L]

omit [FfiSyntax] in
theorem elem_of_granted_recordVote (votes : GMap w64 Bool) (src : w64) (b : Bool) (v : w64) :
    v ∈ granted (recordVote votes src b) →
    v ∈ granted votes ∨ (v = src ∧ b = true) := by
  intro H
  unfold recordVote at H
  cases Hf : votes !! src with
  | some _ => simp only [Hf] at H; exact .inl H
  | none =>
    simp only [Hf] at H
    rw [elem_of_granted] at H ⊢
    by_cases Hv : v = src
    · subst Hv; rw [GMap.lookup_insert_eq] at H; cases H; exact .inr ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hv)] at H; exact .inl H

end ghost

end EtcdGrove
end Perennial
