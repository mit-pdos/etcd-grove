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
module

public import Proof.go_etcd_io.raft.v3.Protocol.Ghost
public import Perennial.Ghost.GhostVar
public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.FUpd

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF]

/-! ### Messages -/

def isMessage (γ : RaftNames) (m : Msg) : IProp GF :=
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
  | .propose =>
      -- a proposal (2026-10-10): a local one (term `0`), a non-empty batch of normal
      -- entries short enough for `appendEntry`, each with its data (`entData`: proposed,
      -- its update deposited before it left the proposing node)
      iprop(⌜m.term = W64 0 ∧ m.entries ≠ [] ∧ (∀ e ∈ m.entries, e.Type' = W32 0) ∧
          (m.entries.length : Int) < 2 ^ 61⌝ ∗
        [∗list] e ∈ m.entries, entData γ e)
  | _ => iprop(True)

instance isMessage_persistent (γ : RaftNames) (m : Msg) :
    Persistent (isMessage (GF := GF) γ m) := by
  unfold isMessage; split <;> (try split) <;> infer_instance

instance isMessage_timeless (γ : RaftNames) (m : Msg) :
    Timeless (isMessage (GF := GF) γ m) := by
  unfold isMessage; split <;> (try split) <;> infer_instance

/-- The message types that carry nothing. -/
def MsgFree (ty : MsgType) : Bool :=
  match ty with
  | .heartbeatResp | .preVote
  | .preVoteResp | .readIndex | .readIndexResp => true
  | _ => false

theorem isMessage_free (γ : RaftNames) (m : Msg) :
    MsgFree m.ty = true → ⊢ isMessage (GF := GF) γ m := by
  intro Hty
  unfold isMessage
  cases h : m.ty <;> simp only [h, MsgFree] at Hty ⊢ <;>
    first | exact absurd Hty (by decide) | exact true_intro

/-- A *rejecting* `voteResp` is free too: it reports no vote. -/
theorem isMessage_reject (γ : RaftNames) (src dst term : w64) :
    ⊢ isMessage (GF := GF) γ (Msg.plain .voteResp src dst term true) := by
  unfold isMessage Msg.plain; exact true_intro

/-- A granting `voteResp` carries the vote it reports, and nothing else. -/
theorem isMessage_grant (γ : RaftNames) (src dst term : w64) :
    isVote (GF := GF) γ src term dst ⊢ isMessage γ (Msg.plain .voteResp src dst term false) := by
  unfold isMessage Msg.plain; exact .rfl

theorem isMessage_grant_inv (γ : RaftNames) (m : Msg) :
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

def leaderWit (γ : RaftNames) (id : w64) (s : PState) : IProp GF :=
  match s.role with
  | .leader => isLeader γ id s.term
  | _ => iprop(True)

instance leaderWit_persistent (γ : RaftNames) (id : w64) (s : PState) :
    Persistent (leaderWit (GF := GF) γ id s) := by
  unfold leaderWit; split <;> infer_instance

instance leaderWit_timeless (γ : RaftNames) (id : w64) (s : PState) :
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
def leadLogOwn (_γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) : IProp GF :=
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

instance leadLogOwn_timeless (γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) :
    Timeless (leadLogOwn (GF := GF) γ s terms) := by
  unfold leadLogOwn; split <;> infer_instance

/-- A leader's `Match` values are backed by acknowledgements. -/
def matchedOk (γ : RaftNames) (s : PState) : IProp GF :=
  match s.role with
  | .leader => iprop([∗map] v ↦ i ∈ s.matched, isAcked γ v s.term i)
  | _ => iprop(True)

instance matchedOk_persistent (γ : RaftNames) (s : PState) :
    Persistent (matchedOk (GF := GF) γ s) := by
  unfold matchedOk; split <;> infer_instance
instance matchedOk_timeless (γ : RaftNames) (s : PState) :
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
def ackOk (γ : RaftNames) (s : PState) (k : w64 × w64) : IProp GF :=
  iprop(∀ (_ : k.1 = s.term ∧ uint.Z s.commit < uint.Z k.2),
    ackAgree γ s.base s.log k.1 k.2)

instance ackOk_persistent (γ : RaftNames) (s : PState) (k : w64 × w64) :
    Persistent (ackOk (GF := GF) γ s k) := by
  unfold ackOk; infer_instance
instance ackOk_timeless (γ : RaftNames) (s : PState) (k : w64 × w64) :
    Timeless (ackOk (GF := GF) γ s k) := by
  unfold ackOk; infer_instance

def acksOk (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) : IProp GF :=
  match s.role with
  | .leader => iprop(True)
  | _ => iprop([∗map] k ↦ _u ∈ acks, ackOk γ s k)

instance acksOk_persistent (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    Persistent (acksOk (GF := GF) γ s acks) := by
  unfold acksOk; split <;> infer_instance
instance acksOk_timeless (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
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

def klOk (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) : IProp GF :=
  match kl with
  | none => iprop(⌜s.role ≠ .leader⌝)
  | some ldr => iprop((∃ q, isWin γ ldr s.term q ∗ ⌜s.vote = W64 0 → id ∉ q⌝) ∗
                ⌜s.role = .leader → ldr = id⌝)

instance klOk_persistent (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) :
    Persistent (klOk (GF := GF) γ id s kl) := by
  unfold klOk; split <;> infer_instance
instance klOk_timeless (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) :
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
def campOwn (γ : RaftNames) (id : w64) (s : PState) (F : List raftpb.Entry) : IProp GF :=
  match s.role with
  | .candidate => isCamp γ id s.term F
  | .leader => iprop(∃ F0, isCamp γ id s.term F0 ∗
       ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
         (plogLast base0 F).term' = s.term⌝)
  | .follower => iprop(True)

instance campOwn_persistent (γ : RaftNames) (id : w64) (s : PState)
    (F : List raftpb.Entry) : Persistent (campOwn (GF := GF) γ id s F) := by
  unfold campOwn; split <;> infer_instance
instance campOwn_timeless (γ : RaftNames) (id : w64) (s : PState)
    (F : List raftpb.Entry) : Timeless (campOwn (GF := GF) γ id s F) := by
  unfold campOwn; split <;> infer_instance

/-- Node `v`'s `k`-th vote-time log: it voted in `T` with full log `F`, knowing the leader
of `T` iff `d` (so its histories then are bounded by `vbnd T d`). -/
def vbnd (T : w64) (d : Bool) : Int := uint.Z T + (if d then 1 else 0)

def isVlog (γ : RaftNames) (v : w64) (k : Nat) (T : w64) (d : Bool)
    (F : List raftpb.Entry) : IProp GF :=
  iprop(∃ γl, ⌜γ.reVlogs !! v = some γl⌝ ∗
    k ↪[γl]□ (((T, d), F) : (w64 × Bool) × List raftpb.Entry))

instance isVlog_persistent (γ : RaftNames) (v : w64) (k : Nat) (T : w64) (d : Bool)
    (F : List raftpb.Entry) : Persistent (isVlog (GF := GF) γ v k T d F) := by
  unfold isVlog; infer_instance
instance isVlog_timeless (γ : RaftNames) (v : w64) (k : Nat) (T : w64) (d : Bool)
    (F : List raftpb.Entry) : Timeless (isVlog (GF := GF) γ v k T d F) := by
  unfold isVlog; infer_instance

/-- A vote-time log has the history of every acknowledgement of an earlier term (all of
them were made before the vote: a node acknowledges only at its own term). -/
def vlogsOk (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)) : IProp GF :=
  iprop([∗map] x ∈ vlogs, ⌜uint.Z x.1.1 ≤ uint.Z s.term⌝ ∗
    [∗map] k ↦ _u ∈ acks, ∀ (_ : uint.Z k.1 < uint.Z x.1.1),
      hist γ x.2 k.1 k.2 (vbnd x.1.1 x.1.2))

instance vlogsOk_persistent (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)) :
    Persistent (vlogsOk (GF := GF) γ s acks vlogs) := by
  unfold vlogsOk; infer_instance

def histsOk (γ : RaftNames) (s : PState) (kl : Option w64) (F : List raftpb.Entry)
    (acks : GMap (w64 × w64) Unit) : IProp GF :=
  iprop([∗map] k ↦ _u ∈ acks, hist γ F k.1 k.2 (bnd s kl))

instance histsOk_persistent (γ : RaftNames) (s : PState) (kl : Option w64)
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
def voteEv (γ : RaftNames) (v T : w64) (d : Bool) (F : List raftpb.Entry) : IProp GF :=
  iprop(∃ γe L0, ⌜γ.reEvs !! v = some γe⌝ ∗ monoListLbOwn γe (L0 ++ [Aev.vote T d F]) ∗
    ∀ (t i : w64), ∀ (_ : Aev.ack t i ∈ L0 ∧ uint.Z t < uint.Z T), hist γ F t i (vbnd T d))

instance voteEv_persistent (γ : RaftNames) (v T : w64) (d : Bool)
    (F : List raftpb.Entry) : Persistent (voteEv (GF := GF) γ v T d F) := by
  unfold voteEv; infer_instance

/-- (Lean addition: Rocq's instance search unfolds `vote_ev` for `vote_just_timeless`.) -/
instance voteEv_timeless (γ : RaftNames) (v T : w64) (d : Bool)
    (F : List raftpb.Entry) : Timeless (voteEv (GF := GF) γ v T d F) := by
  unfold voteEv; infer_instance

/-- The pure part of `ev_pair`: an acknowledgement of an earlier term than a vote, in a
sorted history comparable with the history up to the vote, is before the vote. -/
private theorem ev_pair_pure (L0 La : List Aev) (t i T : w64) (d : Bool) (F : List raftpb.Entry) :
    uint.Z t < uint.Z T → Aev.ack t i ∈ La → EvSorted La →
    (La <+: L0 ++ [Aev.vote T d F] ∨ L0 ++ [Aev.vote T d F] <+: La) →
    Aev.ack t i ∈ L0 := by
  intro HtT Hin Hsort Hp
  rcases Hp with Hp | ⟨R, rfl⟩
  · have := Hp.subset Hin
    simpa using this
  · rcases List.mem_append.mp Hin with Hin | Hin
    · simpa using Hin
    · exfalso
      obtain ⟨p, Hp⟩ := List.mem_iff_getElem?.mp Hin
      have := Hsort L0.length (L0.length + 1 + p) (Aev.vote T d F) (Aev.ack t i) (by omega)
        (by simp) (by
          rw [List.getElem?_append_right (by simp)]
          simpa [show L0.length + 1 + p - (L0.length + 1) = p by omega] using Hp)
      simp only [aevTerm] at this; omega

theorem ev_pair (γ : RaftNames) (v t i T : w64) (d : Bool) (F : List raftpb.Entry) :
    uint.Z t < uint.Z T →
    ⊢ ackEv (GF := GF) γ v t i -∗ voteEv γ v T d F -∗ hist γ F t i (vbnd T d) := by
  intro HtT
  unfold ackEv voteEv
  iintro ⟨%γe, %La, %HLa, #Ha⟩ ⟨%γe', %L0, %Hγe', #Hv, #Hh⟩
  obtain ⟨Hγe, Hin, Hsort⟩ := HLa
  rw [Hγe] at Hγe'; cases Hγe'
  icases mono_list_lb_valid _ _ _ $$ Ha Hv with %Hp
  iapply Hh
  exact ⟨ev_pair_pure L0 La t i T d F HtT Hin Hsort Hp, HtT⟩

def voteJust (γ : RaftNames) (v T c : w64) : IProp GF :=
  iprop(∃ k d Fv Fc, isVlog γ v k T d Fv ∗ isCamp γ c T Fc ∗ logRecs γ base0 Fv ∗
    ⌜PlogWf base0 Fv ∧ plogUpToDate base0 Fv (plogLast base0 Fc) = true⌝ ∗
    (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) ∗
    voteEv γ v T d Fv)

instance voteJust_persistent (γ : RaftNames) (v T c : w64) :
    Persistent (voteJust (GF := GF) γ v T c) := by
  have : ∀ d : Bool, Persistent (PROP := IProp GF)
      (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) :=
    fun _ => inferInstance
  unfold voteJust; infer_instance
instance voteJust_timeless (γ : RaftNames) (v T c : w64) :
    Timeless (voteJust (GF := GF) γ v T c) := by
  have : ∀ d : Bool, Timeless (PROP := IProp GF)
      (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) :=
    fun _ => inferInstance
  unfold voteJust; infer_instance

/-- A node's event history, authoritative: in term order, at or below its term, and every
acknowledgement in it is in its acknowledgement map. -/
def ownEvs (γ : RaftNames) (id T : w64) (acks : GMap (w64 × w64) Unit) : IProp GF :=
  iprop(∃ γe evs, ⌜γ.reEvs !! id = some γe⌝ ∗ monoListAuthOwn γe 1 evs ∗
    ⌜EvSorted evs ∧ (∀ e, e ∈ evs → uint.Z (aevTerm e) ≤ uint.Z T) ∧
      (∀ t i, Aev.ack t i ∈ evs → (acks !! (t, i)).isSome)⌝)

instance ownEvs_timeless (γ : RaftNames) (id T : w64) (acks : GMap (w64 × w64) Unit) :
    Timeless (ownEvs (GF := GF) γ id T acks) := by
  unfold ownEvs; infer_instance

theorem ownEvs_mono (γ : RaftNames) (id T T' : w64) (acks acks' : GMap (w64 × w64) Unit) :
    uint.Z T ≤ uint.Z T' → (∀ k, (acks !! k).isSome → (acks' !! k).isSome) →
    ⊢ ownEvs (GF := GF) γ id T acks -∗ ownEvs γ id T' acks' := by
  intro HT Hsub
  unfold ownEvs
  iintro ⟨%γe, %evs, %Hγe, Ha, %Hs, %Ht, %Hk⟩
  iexists γe, evs
  isplitr; · ipureintro; exact Hγe
  isplitl [Ha]; · iexact Ha
  ipureintro
  refine ⟨Hs, fun e He => ?_, fun t i Hi => Hsub _ (Hk t i Hi)⟩
  have := Ht e He; omega

theorem ownEvs_ack (γ : RaftNames) (id T : w64) (acks : GMap (w64 × w64) Unit) (i : w64) :
    ⊢ ownEvs (GF := GF) γ id T acks ==∗ ownEvs γ id T (<[(T, i) := ()]> acks) ∗ ackEv γ id T i := by
  unfold ownEvs ackEv
  iintro ⟨%γe, %evs, %Hγe, Ha, %Hs, %Ht, %Hk⟩
  imod monoListAuthOwn_update_app [Aev.ack T i] $$ Ha with ⟨Ha, #Hlb⟩
  have Hs' : EvSorted (evs ++ [Aev.ack T i]) :=
    EvSorted_snoc _ _ Hs (fun e He => Ht e He)
  imodintro
  isplitl [Ha]
  · iexists γe, evs ++ [Aev.ack T i]
    isplitr; · ipureintro; exact Hγe
    isplitl [Ha]; · iexact Ha
    ipureintro
    refine ⟨Hs', fun e He => ?_, fun t i' Hi => ?_⟩
    · rcases List.mem_append.mp He with He | He
      · exact Ht e He
      · simp only [List.mem_singleton] at He; subst He; simp [aevTerm]
    · rcases List.mem_append.mp Hi with Hi | Hi
      · by_cases Heq : (T, i) = (t, i')
        · simp [Heq]
        · simp only [GMap.lookup_insert_eq_iff, Heq, ↓reduceIte]; exact Hk t i' Hi
      · simp only [List.mem_singleton, Aev.ack.injEq] at Hi
        obtain ⟨rfl, rfl⟩ := Hi; simp
  · iexists γe, evs ++ [Aev.ack T i]
    isplitr; · ipureintro; exact ⟨Hγe, by simp, Hs'⟩
    iexact Hlb

theorem ownEvs_vote (γ : RaftNames) (id T T' : w64) (acks : GMap (w64 × w64) Unit)
    (d : Bool) (F : List raftpb.Entry) :
    uint.Z T ≤ uint.Z T' →
    ⊢ ownEvs (GF := GF) γ id T acks -∗
      ([∗map] k ↦ _u ∈ acks, ∀ (_ : uint.Z k.1 < uint.Z T'), hist γ F k.1 k.2 (vbnd T' d)) ==∗
      ownEvs γ id T' acks ∗ voteEv γ id T' d F := by
  intro HT
  unfold ownEvs voteEv
  iintro ⟨%γe, %evs, %Hγe, Ha, %Hs, %Ht, %Hk⟩ #Hh
  imod monoListAuthOwn_update_app [Aev.vote T' d F] $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  isplitl [Ha]
  · iexists γe, evs ++ [Aev.vote T' d F]
    isplitr; · ipureintro; exact Hγe
    isplitl [Ha]; · iexact Ha
    ipureintro
    refine ⟨EvSorted_snoc _ _ Hs (fun e He => ?_), fun e He => ?_, fun t i Hi => ?_⟩
    · have := Ht e He; show _ ≤ uint.Z T'; omega
    · rcases List.mem_append.mp He with He | He
      · have := Ht e He; omega
      · simp only [List.mem_singleton] at He; subst He; simp [aevTerm]
    · rcases List.mem_append.mp Hi with Hi | Hi
      · exact Hk t i Hi
      · simp at Hi
  · iexists γe, evs
    isplitr; · ipureintro; exact Hγe
    isplitr; · iexact Hlb
    iintro %t %i %Hin2
    obtain ⟨Hin, Hlt⟩ := Hin2
    obtain ⟨u, Hu⟩ := Option.isSome_iff_exists.mp (Hk t i Hin)
    ihave Hx := BigSepM.bigSepM_lookup (i := (t, i)) Hu $$ Hh
    iapply Hx
    exact Hlt

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

def votesTbl (γ : RaftNames) : IProp GF :=
  iprop([∗map] v ↦ γv ∈ γ.reVotes, ∃ voted : GMap w64 w64,
    ghostMapAuth γv (1 : Qp).half voted ∗ [∗map] T ↦ c ∈ voted, voteJust γ v T c)

instance votesTbl_timeless (γ : RaftNames) : Timeless (votesTbl (GF := GF) γ) := by
  unfold votesTbl; infer_instance

theorem votesTbl_just (γ : RaftNames) (v T c : w64) :
    ⊢ votesTbl (GF := GF) γ -∗ isVote γ v T c -∗ voteJust γ v T c := by
  unfold votesTbl isVote
  iintro Htbl ⟨%γv, %Hγv, #Hf⟩
  icases BigSepM.bigSepM_lookup (i := v) Hγv $$ Htbl with ⟨%voted, Ha, #Hj⟩
  icases ghost_map_lookup $$ Ha Hf with %Hl
  iapply BigSepM.bigSepM_lookup Hl $$ Hj

/-- `ghostMapAuth_agree`, keeping both authorities. -/
private theorem ghostMapAuth_agree_keep {K V : Type} [DecidableEq K] [Pos.Countable K]
    [Pos.Countable V] (γ : GName) (q1 q2 : Qp) (m1 m2 : GMap K V) :
    (ghostMapAuth γ q1 m1 ∗ ghostMapAuth γ q2 m2 : IProp GF) ⊢
      (ghostMapAuth γ q1 m1 ∗ ghostMapAuth γ q2 m2) ∗ ⌜m1 = m2⌝ :=
  persistent_entails_left (by iintro ⟨H1, H2⟩; iapply ghostMapAuth_agree $$ H1 H2)

/-- A whole ghost map authority is two halves. -/
private theorem ghostMapAuth_halves {K V : Type} [DecidableEq K] [Pos.Countable K]
    [Pos.Countable V] (γ : GName) (m : GMap K V) :
    (ghostMapAuth γ 1 m : IProp GF) ⊣⊢
      ghostMapAuth γ (1 : Qp).half m ∗ ghostMapAuth γ (1 : Qp).half m := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (ghostMapAuth_fractional γ m).fractional _ _

theorem votesTbl_insert (γ : RaftNames) (id : w64) (γv : GName) (voted : GMap w64 w64)
    (T c : w64) :
    γ.reVotes !! id = some γv → voted !! T = none →
    ⊢ voteJust (GF := GF) γ id T c -∗ votesTbl γ -∗ ghostMapAuth γv (1 : Qp).half voted ==∗
      votesTbl γ ∗ ghostMapAuth γv (1 : Qp).half (<[T := c]> voted) ∗ T ↪[γv]□ c := by
  intro Hγv Hfree
  unfold votesTbl
  iintro #Hj Htbl Ha
  icases BigSepM.bigSepM_insert_acc (i := id) Hγv $$ Htbl with ⟨⟨%voted', Ha', #Hjs⟩, Hclose⟩
  icombine Ha Ha' as Hab
  icases ghostMapAuth_agree_keep _ _ _ _ _ $$ Hab with ⟨Hab, %Heq⟩
  subst Heq
  ihave Ha := (ghostMapAuth_halves (GF := GF) γv voted).2 $$ Hab
  imod ghost_map_insert_persist T c Hfree $$ Ha with ⟨Ha, #Hf⟩
  icases (ghostMapAuth_halves (GF := GF) γv (<[T := c]> voted)).1 $$ Ha with ⟨Ha, Ha'⟩
  imodintro
  isplitl [Hclose Ha']
  · ihave Hc := Hclose $$ %γv
    have Hid : Std.insert γ.reVotes id γv = γ.reVotes := GMap.insert_id _ _ _ Hγv
    rw [Hid]
    iapply Hc
    iexists (<[T := c]> voted)
    isplitl [Ha']; · iexact Ha'
    iapply (BigSepM.bigSepM_insert (Φ := fun T c => voteJust γ id T c) Hfree).2
    isplitl; · iexact Hj
    iexact Hjs
  isplitl [Ha]; · iexact Ha
  iexact Hf

def committedJust (γ : RaftNames) (l : List raftpb.Entry) : IProp GF :=
  iprop(⌜l = []⌝ ∨ ∃ t n G, cq γ t n G ∗ ⌜l = G.take (uint.Z n).toNat⌝)

instance committedJust_timeless (γ : RaftNames) (l : List raftpb.Entry) :
    Timeless (committedJust (GF := GF) γ l) := by
  unfold committedJust; infer_instance

def raftN : Namespace := nroot .@ "raft_commit"

/-! ### The client log and the proposal registry (2026-10-10)

The client's view of the committed log is `cLog γ L`: the data of the committed client
entries, in commit order, first occurrences only (`firstOcc`, `Model.lean`); a leader's own
entries (the zero slice) do not count. `raftCommitInv` holds one half of the ghost
variable `reCLog`, the client the other: raft cannot move it without the client.

What moves it is the client's **atomic update** for a proposal of data `d`
(`propAu γ d Q`: `AU <{ ∃∃ L, cLog γ L }> @ ⊤ ∖ ↑raftN, ∅ <{ cLog γ (L ++ [d]), COMM Q L }>`),
deposited in the registry before the proposal leaves the proposing node
(`prop_deposit`), and fired by the ghost commit (`commit_extend`) when the first entry
with data `d` is committed -- the linearization point. Each pending slot holds a later
credit with its update: the update is under the invariant's later, and the credit strips
it when the commit fires it (the commit itself is a ghost step, without a later of its
own). A data is deposited once (the fresh token `propFresh γ d`, kept by the invariant);
a retried proposal of the same data carries the persistent `deposited γ d`, and a
duplicate entry (a retry, a redelivered proposal) does not move `cLog`.

A slot `d ↦ (γq, γk)` (`propSlot`) is pending (holding the credit and the update, while
`d ∉ L`) or fired (`d ∈ L`, after the client log `L0` it was fired at), holding the
update's result `Q L0` or, once the client collected it (`prop_collect`), the client's
ticket `γk`. The client's `Q` is tied to the slot by a saved predicate (`isProp`). -/

/-- The client's half of the client log. -/
def cLog (γ : RaftNames) (L : List (List w8)) : IProp GF :=
  ghostVar γ.reCLog (1 : Qp).half L

instance cLog_timeless (γ : RaftNames) (L : List (List w8)) : Timeless (cLog (GF := GF) γ L) := by
  unfold cLog; infer_instance

/-- The token for depositing `d` the first time (an element of the client's map
`reFresh`). -/
def propFresh (γ : RaftNames) (d : List w8) : IProp GF :=
  d ↪[γ.reFresh] ()

instance propFresh_timeless (γ : RaftNames) (d : List w8) :
    Timeless (propFresh (GF := GF) γ d) := by
  unfold propFresh; infer_instance

/-- The client's handle on its deposited proposal: the slot of `d`, with result `Q`. -/
def isProp (γ : RaftNames) (d : List w8) (γp : GName × GName)
    (Q : List (List w8) → IProp GF) : IProp GF :=
  iprop(d ↪[γ.reProps]□ γp ∗ savedPredOwn γp.1 DFrac.discard Q)

/-- The ticket the client trades for the result. -/
def propTok (γp : GName × GName) : IProp GF := token γp.2

instance isProp_persistent (γ : RaftNames) (d : List w8) (γp : GName × GName)
    (Q : List (List w8) → IProp GF) : Persistent (isProp γ d γp Q) := by
  unfold isProp; infer_instance
instance propTok_timeless (γp : GName × GName) : Timeless (propTok (GF := GF) γp) := by
  unfold propTok; infer_instance

theorem isProp_deposited (γ : RaftNames) (d : List w8) (γp : GName × GName)
    (Q : List (List w8) → IProp GF) : ⊢ isProp (GF := GF) γ d γp Q -∗ deposited γ d := by
  unfold isProp deposited
  iintro ⟨#H, -⟩
  iexists γp; iexact H

section inv
variable [InvGS GF]

/-- See the section header. -/
def propAu (γ : RaftNames) (d : List w8) (Q : List (List w8) → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (L : List (List w8)), cLog γ L }> @ ⊤ \ ↑raftN, ∅
          <{ cLog γ (L ++ [d]), COMM Q L }>)

/-- Firing a deposited update: the raft half of the client log, at `Lr`, moves to
`Lr ++ [d]` with the client's half, and the update's result comes out. -/
theorem propAu_fire (γ : RaftNames) (d : List w8) (Q : List (List w8) → IProp GF)
    (Lr : List (List w8)) :
    ⊢ propAu γ d Q -∗ ghostVar γ.reCLog (1 : Qp).half Lr ={⊤ \ ↑raftN}=∗
      ghostVar γ.reCLog (1 : Qp).half (Lr ++ [d]) ∗ Q Lr := by
  iintro Hau Hv
  unfold propAu
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%L', HcL, Hclose⟩
  unfold cLog
  ihave %Heq := ghostVar_agree γ.reCLog Lr (1 : Qp).half L' (1 : Qp).half $$ Hv HcL
  subst Heq
  imod ghostVar_update_halves (Lr ++ [d]) γ.reCLog Lr Lr $$ Hv HcL with ⟨Hv, HcL⟩
  icases Hclose with ⟨-, Hcomm⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcomm
  imod Hcomm $$ HcL with HQ
  imodintro
  iframe Hv HQ

def propSlot (γ : RaftNames) (d : List w8) (γp : GName × GName) (L : List (List w8)) :
    IProp GF :=
  iprop(∃ Q : List (List w8) → IProp GF, savedPredOwn γp.1 DFrac.discard Q ∗
    ( (⌜d ∉ L⌝ ∗ £ 1 ∗ propAu γ d Q)
    ∨ (∃ L0, ⌜L0 ++ [d] <+: L ∧ d ∉ L0⌝ ∗ (Q L0 ∨ token γp.2)) ))

/-- The registry and the client log, for the committed log `l`: each committed entry's
data (`ods`), the raft half of the client log at `firstOcc ods`, and the slots (each
holding its data's fresh token). -/
def propsOwn (γ : RaftNames) (l : List raftpb.Entry) (R : GMap (List w8) (GName × GName)) :
    IProp GF :=
  iprop(∃ (ods : List (Option (List w8))),
    ([∗list] e;o ∈ l;ods, entDataIs γ e o) ∗
    ghostVar γ.reCLog (1 : Qp).half (firstOcc ods) ∗
    ghostMapAuth γ.reProps 1 R ∗
    [∗map] d ↦ γp ∈ R, propSlot γ d γp (firstOcc ods) ∗ propFresh γ d)

def raftCommitInv (γ : RaftNames) : IProp GF :=
  inv raftN iprop(∃ l, ∃ (R : GMap (List w8) (GName × GName)),
               ownCommitted γ l ∗ committedJust γ l ∗ votesTbl γ ∗ propsOwn γ l R)

instance raftCommitInv_persistent (γ : RaftNames) :
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

def ownLogGhost (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) : IProp GF :=
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

def ownRaftGhost (γ : RaftNames) (id : w64) (s : PState) : IProp GF :=
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

theorem ownRaftGhost_intro (γ : RaftNames) (id : w64) (s : PState) (γv : GName)
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
theorem ownRaftGhost_lead_ok (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜LeadOk id s⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hlead_ok

/-- A follower's tally is empty. -/
theorem ownRaftGhost_follower_votes (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜FollowerVotesOk s⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hfollower_votes

theorem matchedOk_eq (γ : RaftNames) (s1 s2 : PState) :
    s2.role = s1.role →
    s2.term = s1.term →
    s2.matched = s1.matched →
    ⊢ matchedOk (GF := GF) γ s1 -∗ matchedOk γ s2 := by
  intro H1 H2 H3
  unfold matchedOk; rw [H1, H2, H3]
  iintro H; iexact H

theorem ownRaftGhost_excl (γ : RaftNames) (id : w64) (s1 s2 : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s1 -∗ ownRaftGhost γ id s2 -∗ False := by
  -- the vote map is half the node's since 2026-10-05; the term-log map is whole
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γ1, %v1, %k1, H1⟩ ⟨%γ2, %v2, %k2, H2⟩
  icases H1 with ⟨_, _, _, _, _, _, _, _, ⟨%γm1, %t1, H1⟩, _⟩
  icases H2 with ⟨_, _, _, _, _, _, _, _, ⟨%γm2, %t2, H2⟩, _⟩
  icases H1 with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %Hn1, H1, _⟩
  icases H2 with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %Hn2, H2, _⟩
  rw [Hn1] at Hn2; cases Hn2
  icases ghostMapAuth_valid_2 _ _ _ _ _ $$ H1 H2 with %Hq
  exfalso; have := Hq.1; simp at this; grind

/-- Everything in a node's outbox was legitimately put there. -/
theorem ownRaftGhost_outbox (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ([∗list] m ∈ s.outbox, isMessage γ m) := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iexact Hout

theorem ownRaftGhost_isLeader (γ : RaftNames) (id : w64) (s : PState) :
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
