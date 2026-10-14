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
variable {md : Bool}

/-! ### Read-index (2026-10-12; see `Protocol/ReadIndex.lean`) -/

/-- The read context `c` was created knowing the committed log `Lc`. -/
def readReq (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) : IProp GF :=
  iprop(c ↪[γ.reReads]□ Lc ∗ isCommitted γ Lc)

instance readReq_persistent (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) :
    Persistent (readReq (GF := GF) γ c Lc) := by
  unfold readReq; infer_instance

/-- What a `ReadState{Index: i, RequestCtx: c}` promises: the log `c` was created with is no
longer than `i`. -/
def readOk (γ : RaftNames) (c : List w8) (i : w64) : IProp GF :=
  iprop(∃ Lc, readReq γ c Lc ∗ ⌜(Lc.length : Int) ≤ uint.Z i⌝)

instance readOk_persistent (γ : RaftNames) (c : List w8) (i : w64) :
    Persistent (readOk (GF := GF) γ c i) := by
  unfold readOk; infer_instance

/-- A leader's record of a request: its context and read index, and whether it was doomed
at arrival (the term and quorum of the acknowledgements that doomed it). -/
abbrev RqRec := (List w8 × w64) × Option (w64 × GSet w64)

/-- A record doomed by a commit fact of a term `t'` above `T` at a nonzero index (the doom
fact, `cqAt`, with its configuration data; since 2026-10-14, reconfiguration stage B4). The
record's set `U` holds the doom fact's quorum and (since stage B5, dynamic mode) the quorums of
the doom fact's witnesses of terms above `T` (the paper's section 8, case `j_r ≤ j_m - 2`), every
member of which acknowledged at a term above `T`: a node at term `T` is in none of them
(`ownRaftGhost_not_doomed`). The doom fact's witnesses are restated with that inclusion (the
arrival chose them, `doomed_intro`). -/
def doomed (γ : RaftNames) (T t' : w64) (U : GSet w64) : IProp GF :=
  iprop(∃ n G a c q, ⌜uint.Z T < uint.Z t' ∧ 0 < uint.Z n ∧ ∀ x, x ∈ q → x ∈ U⌝ ∗
    cqAt γ t' n G a c q ∗
    (∀ (u : w64), ∀ (_ : u ∈ U), ∃ (t'' i'' : w64),
      ⌜uint.Z T < uint.Z t'' ∧ 0 < uint.Z i''⌝ ∗ isAcked γ u t'' i'') ∗
    dynOn γ iprop(∀ (k : Nat), ∀ (_ : IsConfPos G k ∧ k < (uint.Z a).toNat),
      ∃ (tw nw : w64) (Gw : List raftpb.Entry) (aw : w64) (cw : CfgM) (qw : GSet w64),
        ⌜WitOk G k tw nw Gw aw (uint.Z t' + 1) ∧ (uint.Z T < uint.Z tw → ∀ x, x ∈ qw → x ∈ U)⌝ ∗
        cqAt γ tw nw Gw aw cw qw))

instance doomed_persistent (γ : RaftNames) (T t' : w64) (q : GSet w64) :
    Persistent (doomed (GF := GF) γ T t' q) := by
  unfold doomed
  refine exists_persistent _ (h := fun n => ?_)
  refine exists_persistent _ (h := fun G => ?_)
  refine exists_persistent _ (h := fun a => ?_)
  refine exists_persistent _ (h := fun c => ?_)
  refine exists_persistent _ (h := fun q1 => ?_)
  refine @sep_persistent _ _ _ _ inferInstance ?_
  refine @sep_persistent _ _ _ _ inferInstance ?_
  refine @sep_persistent _ _ _ _ ?_ ?_
  · refine forall_persistent _ (h := fun u => ?_)
    refine forall_persistent _ (h := fun hu => ?_)
    infer_instance
  · exact dynOn_persistent _ _

def rqRecOk (γ : RaftNames) (T : w64) (r : RqRec) : IProp GF :=
  match r.2 with
  | none => readOk γ r.1.1 r.1.2
  | some p => doomed γ T p.1 p.2

instance rqRecOk_persistent (γ : RaftNames) (T : w64) (r : RqRec) :
    Persistent (rqRecOk (GF := GF) γ T r) := by
  unfold rqRecOk; split <;> infer_instance

instance readReq_timeless (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) :
    Timeless (readReq (GF := GF) γ c Lc) := by
  unfold readReq; infer_instance
instance readOk_timeless (γ : RaftNames) (c : List w8) (i : w64) :
    Timeless (readOk (GF := GF) γ c i) := by
  unfold readOk; infer_instance

instance doomed_timeless (γ : RaftNames) (T t' : w64) (q : GSet w64) :
    Timeless (doomed (GF := GF) γ T t' q) := by
  unfold doomed; infer_instance

instance rqRecOk_timeless (γ : RaftNames) (T : w64) (r : RqRec) :
    Timeless (rqRecOk (GF := GF) γ T r) := by
  unfold rqRecOk; split <;> infer_instance

/-- The registry of the read requests the leader `L` of `T` recorded, at least `recs`. -/
def rqLb (γ : RaftNames) (L T : w64) (recs : List RqRec) : IProp GF :=
  iprop(∃ γl γq, ⌜γ.reRdq !! L = some γl⌝ ∗ T ↪[γl]□ γq ∗ monoListLbOwn γq recs)

instance rqLb_persistent (γ : RaftNames) (L T : w64) (recs : List RqRec) :
    Persistent (rqLb (GF := GF) γ L T recs) := by
  unfold rqLb; infer_instance
instance rqLb_timeless (γ : RaftNames) (L T : w64) (recs : List RqRec) :
    Timeless (rqLb (GF := GF) γ L T recs) := by
  unfold rqLb; infer_instance

/-- A follower `v`'s acknowledgement of the first `q` of the leader's records: none of them
is doomed by a quorum containing `v`. -/
def HbAckOk (v : w64) (q : Nat) (recs : List RqRec) : Prop :=
  q ≤ recs.length ∧ ∀ r ∈ recs.take q, ∀ t' qq, r.2 = some (t', qq) → v ∉ qq

/-! ### Campaign records' dynamic facts (2026-10-14, reconfiguration stage B5)

What the dynamic proof needs of a campaign `(F, k)` of `c` in `T`, beyond `isCampK` (which sits
below the commit facts and cannot name them): I1 of the campaign log at `k` (`RInv`'s, at the
campaign), its records, and the candidate's `commitIn` of `k` at a term below `T` -- the
commit fact that justifies `k` and the witnesses of the conf entries below `k` (the paper's
repair 3). A vote request carries it (`isMessage`), and so does every vote cast for the
candidate (`voteJust`): the winners' are found through their votes. -/
def campDyn (γ : RaftNames) (c T : w64) (F : List raftpb.Entry) : IProp GF :=
  iprop(∃ (k tm : w64), ⌜uint.Z tm < uint.Z T ∧ ConfI1 F (uint.Z k).toNat ∧ PlogWf base0 F⌝ ∗
    isCampK γ c T F k ∗ logRecs γ base0 F ∗ commitIn γ F k tm)

instance campDyn_persistent (γ : RaftNames) (c T : w64) (F : List raftpb.Entry) :
    Persistent (campDyn (GF := GF) γ c T F) := by
  unfold campDyn; infer_instance
instance campDyn_timeless (γ : RaftNames) (c T : w64) (F : List raftpb.Entry) :
    Timeless (campDyn (GF := GF) γ c T F) := by
  unfold campDyn; infer_instance

/-! ### Messages -/

def isMessage (γ : RaftNames) (m : Msg) : IProp GF :=
  match m.ty with
  | .vote =>
      -- the candidate's campaign record, whose last entry the request reports
      -- (2026-10-03)
      iprop(∃ Fc, isCamp γ m.src m.term Fc ∗
        ⌜plogLast base0 Fc = entryID.mk m.logterm m.index⌝ ∗
        -- (2026-10-14, stage B5) the campaign's dynamic facts
        dynOn γ (campDyn γ m.src m.term Fc))
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
      ⌜m.src ≠ W64 0⌝ ∗
      -- (2026-10-12) a read-index position: the leader's registry up to it
      (⌜m.ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜m.ctx = u64Le q ∧ uint.nat q ≤ recs.length⌝ ∗ rqLb γ m.src m.term recs ∗
         [∗list] r ∈ recs, rqRecOk γ m.term r))
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
      -- a proposal (2026-10-10): a local one (term `0`), a non-empty batch short enough
      -- for `appendEntry`, each entry with its data (`entData`: a normal entry's proposed,
      -- its update deposited before it left the proposing node; since 2026-10-13 also
      -- conf-change entries, whose bytes decode -- until then normal entries only)
      iprop(⌜m.term = W64 0 ∧ m.entries ≠ [] ∧
          (m.entries.length : Int) < 2 ^ 61⌝ ∗
        [∗list] e ∈ m.entries, entData γ e)
  -- (2026-10-12) read-index: a heartbeat response's position, acknowledged; a request's
  -- context, created; a response's read index, at least its context's log
  | .heartbeatResp =>
      iprop(⌜m.ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
        ⌜m.ctx = u64Le q ∧ HbAckOk m.src (uint.nat q) recs⌝ ∗ rqLb γ m.dst m.term recs)
  | .readIndex =>
      iprop(∃ e c Lc, ⌜m.entries = [e]⌝ ∗ isPropData γ e.Data' c ∗ readReq γ c Lc)
  | .readIndexResp =>
      iprop(∃ e c, ⌜m.entries = [e]⌝ ∗ isPropData γ e.Data' c ∗ readOk γ c m.index)
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
  | .preVote | .preVoteResp => true
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
def leadLogOwn (γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) : IProp GF :=
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
    voteEv γ v T d Fv ∗
    -- (2026-10-14, stage B5) the candidate's campaign's dynamic facts
    dynOn γ (campDyn γ c T Fc))

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
  iprop(⌜l = []⌝ ∨ ∃ t n G ldr, cq γ t n G ∗ ⌜l = G.take (uint.Z n).toNat⌝ ∗
    -- (2026-10-12, read-index) the leader of `t` whose commit extended the log to `n`,
    -- and its commit lower bound for `t`
    isLeader γ ldr t ∗ cmtLb γ ldr t n)

instance committedJust_timeless (γ : RaftNames) (l : List raftpb.Entry) :
    Timeless (committedJust (GF := GF) γ l) := by
  unfold committedJust; infer_instance

instance committedJust_persistent (γ : RaftNames) (l : List raftpb.Entry) :
    Persistent (committedJust (GF := GF) γ l) := by
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

/-- The winners table (2026-10-14, reconfiguration stage B4): the authority of `reTbl`, each
entry with its winner's record (and the entry's persistent element). -/
def winTbl (γ : RaftNames) : IProp GF :=
  iprop(∃ W : GMap w64 WinRec, ghostMapAuth γ.reTbl 1 W ∗
    [∗map] T ↦ r ∈ W, isWinCore γ r.1.1 T r.1.2 r.2 ∗ T ↪[γ.reTbl]□ r)

instance winTbl_timeless (γ : RaftNames) : Timeless (winTbl (GF := GF) γ) := by
  unfold winTbl; infer_instance

def raftCommitInv (γ : RaftNames) : IProp GF :=
  inv raftN iprop(∃ l, ∃ (R : GMap (List w8) (GName × GName)),
               ownCommitted γ l ∗ committedJust γ l ∗ votesTbl γ ∗ propsOwn γ l R ∗
               winTbl γ)

instance raftCommitInv_persistent (γ : RaftNames) :
    Persistent (raftCommitInv (GF := GF) γ) := by
  unfold raftCommitInv; infer_instance

/-- A node's committed prefix: the first `commit` entries of its full log `fp ++ log` (the
entries at indices `1 .. commit`). -/
def cprefix (fp : List raftpb.Entry) (s : PState) : List raftpb.Entry :=
  (fp ++ s.log).take (uint.Z s.commit).toNat

/-! ### The commit lower bounds of the terms a node led (2026-10-12, read-index)

`lcmOwn γ id s`: node `id`'s map `term ↦ γc` (`reLcm`), with its keys as `TermsOk`'s, and,
while it leads, the authority of its current term's lower bound, at most its commit index.
The leader's commit raises it (`lcmOwn_commit`), which gives the global log's
justification its `cmtLb`; a leader of `T` reads every `cmtLb` of its own `T` as at most
its commit index (`lcmOwn_bound`). -/

theorem uint_nat_eq (w : w64) : (uint.nat w : Int) = uint.Z w := by
  simp [uint.nat, uint.Z]

theorem uint_nat_le_of_Z_le {a b : w64} (h : uint.Z a ≤ uint.Z b) : uint.nat a ≤ uint.nat b := by
  simp only [uint.nat, uint.Z] at *; omega

def LcmOk (lcm : GMap w64 GName) (s : PState) : Prop :=
  ∀ t, (lcm !! t).isSome →
    uint.Z t < uint.Z s.term ∨
    (t = s.term ∧ s.role = .leader)

def lcmLead (s : PState) (lcm : GMap w64 GName) : IProp GF :=
  match s.role with
  | .leader => iprop(∃ γc c, ⌜lcm !! s.term = some γc⌝ ∗ monoNatAuthOwn γc 1 c ∗
      ⌜c ≤ uint.nat s.commit⌝)
  | _ => iprop(True)

instance lcmLead_timeless (s : PState) (lcm : GMap w64 GName) :
    Timeless (lcmLead (GF := GF) s lcm) := by
  unfold lcmLead; split <;> infer_instance

theorem lcmLead_leader (s : PState) (lcm : GMap w64 GName) (h : s.role = .leader) :
    lcmLead (GF := GF) s lcm = iprop(∃ γc c, ⌜lcm !! s.term = some γc⌝ ∗
      monoNatAuthOwn γc 1 c ∗ ⌜c ≤ uint.nat s.commit⌝) := by
  unfold lcmLead; rw [h]

theorem lcmLead_nl (s : PState) (lcm : GMap w64 GName) (h : s.role ≠ .leader) :
    lcmLead (GF := GF) s lcm = iprop(True) := by
  unfold lcmLead; split
  · contradiction
  · rfl

def lcmOwn (γ : RaftNames) (id : w64) (s : PState) : IProp GF :=
  iprop(∃ γl, ∃ (lcm : GMap w64 GName), ⌜γ.reLcm !! id = some γl⌝ ∗
    ghostMapAuth γl 1 lcm ∗ ([∗map] t ↦ γc ∈ lcm, t ↪[γl]□ γc) ∗
    ⌜LcmOk lcm s⌝ ∗ lcmLead s lcm)

instance lcmOwn_timeless (γ : RaftNames) (id : w64) (s : PState) :
    Timeless (lcmOwn (GF := GF) γ id s) := by
  unfold lcmOwn; infer_instance

/-- Across a step: a leader stays one only within its term, leaves a term only for a
higher one, and the commit index does not move back. -/
theorem lcmOwn_mono (γ : RaftNames) (id : w64) (s s' : PState) :
    (s'.role = .leader → s.role = .leader ∧ s'.term = s.term) →
    (s'.role ≠ .leader → s.role = .leader → uint.Z s.term < uint.Z s'.term) →
    uint.Z s.term ≤ uint.Z s'.term →
    uint.Z s.commit ≤ uint.Z s'.commit →
    lcmOwn (GF := GF) γ id s ⊢ lcmOwn γ id s' := by
  intro Hlead Hdown Hle Hcm
  unfold lcmOwn
  iintro ⟨%γl, %lcm, %Hγl, Ha, #Hf, %Hok, Hl⟩
  iexists γl, lcm
  iframe Ha Hf
  isplitr; · ipureintro; exact Hγl
  isplitr
  · ipureintro
    intro t Ht
    rcases Hok t Ht with Hlt | ⟨rfl, Hr⟩
    · left; omega
    · by_cases Hr' : s'.role = .leader
      · obtain ⟨-, Hte⟩ := Hlead Hr'; right; exact ⟨Hte.symm, Hr'⟩
      · left; exact Hdown Hr' Hr
  by_cases Hr' : s'.role = .leader
  · obtain ⟨Hr, Hte⟩ := Hlead Hr'
    rw [lcmLead_leader s lcm Hr, lcmLead_leader s' lcm Hr', Hte]
    icases Hl with ⟨%γc, %c, %Hc, Hac, %Hcle⟩
    iexists γc, c
    iframe Hac
    ipureintro
    refine ⟨Hc, ?_⟩
    have := uint_nat_le_of_Z_le Hcm
    omega
  · rw [lcmLead_nl s' lcm Hr']
    ipureintro; trivial

/-- A candidate that wins its term allocates the term's lower bound, at its commit
index. -/
theorem lcmOwn_win (γ : RaftNames) (id : w64) (s s' : PState) :
    s.role ≠ .leader → s'.role = .leader → s'.term = s.term →
    uint.Z s.commit ≤ uint.Z s'.commit →
    lcmOwn (GF := GF) γ id s ⊢ |==> lcmOwn γ id s' := by
  intro Hr Hr' Hte Hcm
  unfold lcmOwn
  iintro ⟨%γl, %lcm, %Hγl, Ha, #Hf, %Hok, -⟩
  have Hfree : lcm !! s.term = none := by
    cases h : lcm !! s.term with
    | none => rfl
    | some _ =>
      rcases Hok s.term (by simp [h]) with Hlt | ⟨-, Hl⟩
      · omega
      · exact absurd Hl Hr
  imod mono_nat_own_alloc (GF := GF) (uint.nat s.commit) with ⟨%γc, Hac, -⟩
  imod ghost_map_insert_persist s.term γc Hfree $$ Ha with ⟨Ha, #Hfc⟩
  imodintro
  iexists γl, (<[s.term := γc]> lcm)
  iframe Ha
  isplitr; · ipureintro; exact Hγl
  isplitr
  · iapply (BigSepM.bigSepM_insert (Φ := fun t γc => iprop(t ↪[γl]□ γc)) Hfree).2
    isplitr; · iexact Hfc
    iexact Hf
  isplitr
  · ipureintro
    intro t Ht
    by_cases Htt : s.term = t
    · subst Htt; right; exact ⟨Hte.symm, Hr'⟩
    · rw [GMap.lookup_insert_ne _ _ Htt] at Ht
      rcases Hok t Ht with Hlt | ⟨rfl, Hl⟩
      · left; rw [Hte]; exact Hlt
      · exact absurd Hl Hr
  rw [lcmLead_leader s' _ Hr', Hte]
  iexists γc, uint.nat s.commit
  iframe Hac
  ipureintro
  refine ⟨by simp, uint_nat_le_of_Z_le Hcm⟩

/-- A leader's commit moving up to `n`: the lower bound follows, and gives `cmtLb`. -/
theorem lcmOwn_commit (γ : RaftNames) (id : w64) (s s' : PState) (n : w64) :
    s.role = .leader → s'.role = .leader → s'.term = s.term → s'.commit = n →
    uint.Z s.commit ≤ uint.Z n →
    lcmOwn (GF := GF) γ id s ⊢ |==> (lcmOwn γ id s' ∗ cmtLb γ id s.term n) := by
  intro Hr Hr' Hte Hc Hle
  unfold lcmOwn
  iintro ⟨%γl, %lcm, %Hγl, Ha, #Hf, %Hok, Hl⟩
  rw [lcmLead_leader s lcm Hr]
  icases Hl with ⟨%γc, %c, %Hγc, Hac, %Hcle⟩
  have Hcn : c ≤ uint.nat n := by have := uint_nat_le_of_Z_le Hle; omega
  ihave Hup := mono_nat_own_update (GF := GF) (γ := γc) (n := c) (uint.nat n) Hcn $$ Hac
  imod Hup with ⟨Hac, #Hlb⟩
  ihave #Hfc := BigSepM.bigSepM_lookup (Φ := fun t γc => iprop(t ↪[γl]□ γc)) Hγc $$ Hf
  imodintro
  isplitl [Ha Hac]
  · iexists γl, lcm
    iframe Ha Hf
    isplitr; · ipureintro; exact Hγl
    isplitr
    · ipureintro
      intro t Ht
      rcases Hok t Ht with Hlt | ⟨rfl, -⟩
      · left; rw [Hte]; exact Hlt
      · right; exact ⟨Hte.symm, Hr'⟩
    rw [lcmLead_leader s' lcm Hr', Hte]
    iexists γc, uint.nat n
    iframe Hac
    ipureintro
    exact ⟨Hγc, by rw [Hc]; exact Nat.le_refl _⟩
  · unfold cmtLb
    iexists γl, γc
    iframe Hfc Hlb
    ipureintro; exact Hγl

/-- A leader of `T` holds every commit lower bound of its own `T` to its commit index. -/
theorem lcmOwn_bound (γ : RaftNames) (id : w64) (s : PState) (n : w64) :
    s.role = .leader →
    ⊢ lcmOwn (GF := GF) γ id s -∗ cmtLb γ id s.term n -∗ ⌜uint.Z n ≤ uint.Z s.commit⌝ := by
  intro Hr
  unfold lcmOwn cmtLb
  iintro ⟨%γl, %lcm, %Hγl, Ha, #Hf, %Hok, Hl⟩ ⟨%γl', %γc', %Hγl', #Hfc', #Hlb⟩
  rw [Hγl] at Hγl'; cases Hγl'
  rw [lcmLead_leader s lcm Hr]
  icases Hl with ⟨%γc, %c, %Hγc, Hac, %Hcle⟩
  ihave #Hfc := BigSepM.bigSepM_lookup (Φ := fun t γc => iprop(t ↪[γl]□ γc)) Hγc $$ Hf
  icases ghostMapElem_agree $$ Hfc Hfc' with %Heq
  subst Heq
  ihave %Hv := monoNatLbOwn_valid γc 1 c (uint.nat n) $$ Hac Hlb
  ipureintro
  have h1 : (uint.nat n : Int) = uint.Z n := by simp [uint.nat, uint.Z]
  have h2 : (uint.nat s.commit : Int) = uint.Z s.commit := by simp [uint.nat, uint.Z]
  have h3 : (uint.nat n : Int) ≤ c := by exact_mod_cast Hv.2
  have h4 : (c : Int) ≤ uint.nat s.commit := by exact_mod_cast Hcle
  omega

/-- `lcmOwn_bound`, keeping the lower bounds. -/
theorem lcmOwn_bound_keep (γ : RaftNames) (id : w64) (s : PState) (n : w64) :
    s.role = .leader →
    ⊢ lcmOwn (GF := GF) γ id s -∗ cmtLb γ id s.term n -∗
      lcmOwn γ id s ∗ ⌜uint.Z n ≤ uint.Z s.commit⌝ := by
  intro Hr
  unfold lcmOwn cmtLb
  iintro ⟨%γl, %lcm, %Hγl, Ha, #Hf, %Hok, Hl⟩ ⟨%γl', %γc', %Hγl', #Hfc', #Hlb⟩
  rw [Hγl] at Hγl'; cases Hγl'
  rw [lcmLead_leader s lcm Hr]
  icases Hl with ⟨%γc, %c, %Hγc, Hac, %Hcle⟩
  ihave #Hfc := BigSepM.bigSepM_lookup (Φ := fun t γc => iprop(t ↪[γl]□ γc)) Hγc $$ Hf
  icases ghostMapElem_agree $$ Hfc Hfc' with %Heq
  subst Heq
  ihave %Hv := monoNatLbOwn_valid γc 1 c (uint.nat n) $$ Hac Hlb
  isplitl
  · iexists γl, lcm
    iframe Ha Hf
    isplitr; · ipureintro; exact Hγl
    isplitr; · ipureintro; exact Hok
    rw [lcmLead_leader s lcm Hr]
    iexists γc, c
    iframe Hac
    ipureintro; exact ⟨Hγc, Hcle⟩
  ipureintro
  have h1 : (uint.nat n : Int) = uint.Z n := by simp [uint.nat, uint.Z]
  have h2 : (uint.nat s.commit : Int) = uint.Z s.commit := by simp [uint.nat, uint.Z]
  have h3 : (uint.nat n : Int) ≤ c := by exact_mod_cast Hv.2
  have h4 : (c : Int) ≤ uint.nat s.commit := by exact_mod_cast Hcle
  omega

/-! ### The read-index ghost state of a node (2026-10-12, notes/decisions.md, "Read-index")

`rdOwn γ id s` is about `s.rd`, the read state the protocol reads off the node:
- `reRdq`'s map `term ↦ γq` of the registries of the terms it led (keys as `TermsOk`'s);
- while it leads, the registry of its term: the records (`RqRec`) of every request it
  queued in the term, each with its `rqRecOk`; the queue is the registry's tail past
  `confirmed`, each request's index and context its record's; every acknowledgement in
  `acks` is a position its voter acknowledged (`HbAckOk`); and the credits the requests
  brought, as many as records (which bounds the positions);
- a non-leader's read-only object is the fresh one;
- each `ReadState` read at least its context's log (`readOk`);
- each pending request a created context and a credit;
- one credit per `MsgReadIndex` in the outbox;
- the credits' invariant. -/

def rdCredN : Namespace := nroot .@ "raft_read_credits"

/-- `n` read credits. -/
def rdCred (γ : RaftNames) (n : Nat) : IProp GF :=
  own γ.reRdCred (◯ n : Auth Nat)

/-- The credits handed out are fewer than `2^64 - 1`. -/
def rdCredInv (γ : RaftNames) : IProp GF :=
  inv rdCredN iprop(∃ B : Nat, own γ.reRdCred (● B : Auth Nat) ∗ ⌜B < 2 ^ 64 - 1⌝)

instance rdCredInv_persistent (γ : RaftNames) : Persistent (rdCredInv (GF := GF) γ) := by
  unfold rdCredInv; infer_instance

theorem rdCred_split (γ : RaftNames) (a b : Nat) :
    rdCred (GF := GF) γ (a + b) ⊣⊢ rdCred γ a ∗ rdCred γ b := by
  unfold rdCred
  rw [show (◯ (a + b) : Auth Nat) = (◯ a) • (◯ b) from Auth.frag_op]
  exact own_op γ.reRdCred _ _

/-- No read credit. -/
theorem rdCred_zero_upd (γ : RaftNames) : ⊢ |==> rdCred (GF := GF) γ 0 := by
  unfold rdCred
  exact own_unit _

/-- The credits handed out are fewer than `2^64 - 1`. -/
theorem rdCred_bound (γ : RaftNames) (n : Nat) (E : CoPset) (HE : ↑rdCredN ⊆ E) :
    ⊢ rdCredInv (GF := GF) γ -∗ rdCred γ n ={E}=∗ rdCred γ n ∗ ⌜n < 2 ^ 64 - 1⌝ := by
  iintro #Hinv Hcr
  unfold rdCredInv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%B, HB, %Hb⟩
  unfold rdCred
  icombine HB Hcr gives %Hv
  have Hle : n ≤ B := by
    obtain ⟨z, hz⟩ := (Auth.auth_both_valid_discrete.mp Hv).1
    have : B = n + z := hz
    omega
  imod Hclose $$ [HB] with -
  · inext
    iexists B
    iframe HB
    ipureintro; exact Hb
  imodintro
  iframe Hcr
  ipureintro; omega

theorem HbAckOk_app (v : w64) (q : Nat) (recs more : List RqRec) :
    HbAckOk v q recs → HbAckOk v q (recs ++ more) := by
  intro ⟨h1, h2⟩
  refine ⟨by simp; omega, ?_⟩
  rw [List.take_append_of_le_length h1]
  exact h2

theorem HbAckOk_le (v : w64) (q q' : Nat) (recs : List RqRec) :
    q' ≤ q → HbAckOk v q recs → HbAckOk v q' recs := by
  intro hle ⟨h1, h2⟩
  refine ⟨by omega, fun r hr => h2 r ?_⟩
  exact (List.take_subset_take_left _ hle) hr

theorem HbAckOk_w64Max (v x y : w64) (recs : List RqRec) :
    HbAckOk v (uint.nat x) recs → HbAckOk v (uint.nat y) recs →
    HbAckOk v (uint.nat (w64Max x y)) recs := by
  intro hx hy; unfold w64Max; split <;> assumption

theorem HbAckOk_zero (v : w64) (recs : List RqRec) : HbAckOk v 0 recs :=
  ⟨Nat.zero_le _, fun r hr => by simp at hr⟩

/-- What a confirmed request's answer needs (2026-10-13): its entry, a proposed slice whose
context `c` the index reads (`readOk`). -/
def respFacts (γ : RaftNames) (q : ReadReq) : IProp GF :=
  iprop(∃ e c, ⌜q.ents = [e]⌝ ∗ isPropData γ e.Data' c ∗ readOk γ c q.index)

instance respFacts_persistent (γ : RaftNames) (q : ReadReq) :
    Persistent (respFacts (GF := GF) γ q) := by
  unfold respFacts; infer_instance

/-- How many read-index requests a list of messages holds. -/
def rdCount (ms : List Msg) : Nat := ms.countP (fun m => decide (m.ty = .readIndex))

theorem rdCount_append (a b : List Msg) : rdCount (a ++ b) = rdCount a + rdCount b := by
  unfold rdCount; exact List.countP_append

theorem rdCount_singleton (m : Msg) : rdCount [m] = if m.ty = .readIndex then 1 else 0 := by
  unfold rdCount; by_cases h : m.ty = .readIndex <;> simp [h]

/-- A `ReadState` handed out (2026-10-13): its context is a slice proposed holding `c`,
and its index is at least the log `c` was created knowing (`readOk`). -/
def readStateOk (γ : RaftNames) (st : ReadState) : IProp GF :=
  iprop(∃ c, isPropData γ st.RequestCtx' c ∗ readOk γ c st.Index')

instance readStateOk_persistent (γ : RaftNames) (st : ReadState) :
    Persistent (readStateOk (GF := GF) γ st) := by
  unfold readStateOk; infer_instance

def rdLead (γ : RaftNames) (s : PState) (rqm : GMap w64 GName) : IProp GF :=
  match s.role with
  | .leader => iprop(∃ γq, ∃ (recs : List RqRec), ⌜rqm !! s.term = some γq⌝ ∗
      monoListAuthOwn γq 1 recs ∗
      ([∗list] r ∈ recs, rqRecOk γ s.term r) ∗
      ⌜recs.length = uint.nat s.rd.ro.confirmed + s.rd.ro.pending.length⌝ ∗
      ([∗list] k ↦ q ∈ s.rd.ro.pending, ∃ r e,
         ⌜recs[uint.nat s.rd.ro.confirmed + k]? = some r ∧ q.index = r.1.2 ∧ q.ents = [e]⌝ ∗
         isPropData γ e.Data' r.1.1) ∗
      ⌜∀ v a, s.rd.ro.acks !! v = some a → HbAckOk v (uint.nat a) recs⌝ ∗
      rdCred γ recs.length)
  | _ => iprop(⌜s.rd.ro = ⟨[], ∅, W64 0⟩⌝)

instance rdLead_timeless (γ : RaftNames) (s : PState) (rqm : GMap w64 GName) :
    Timeless (rdLead (GF := GF) γ s rqm) := by
  unfold rdLead rdCred; split <;> infer_instance

theorem rdLead_nl (γ : RaftNames) (s : PState) (rqm : GMap w64 GName) (h : s.role ≠ .leader) :
    rdLead (GF := GF) γ s rqm = iprop(⌜s.rd.ro = ⟨[], ∅, W64 0⟩⌝) := by
  unfold rdLead; split
  · contradiction
  · rfl

def rdOwn (γ : RaftNames) (id : w64) (s : PState) : IProp GF :=
  iprop(∃ γl, ∃ (rqm : GMap w64 GName), ⌜γ.reRdq !! id = some γl⌝ ∗
    ghostMapAuth γl 1 rqm ∗ ([∗map] t ↦ γq ∈ rqm, t ↪[γl]□ γq) ∗
    ⌜LcmOk rqm s⌝ ∗ rdLead γ s rqm ∗
    ([∗list] st ∈ s.rd.states, readStateOk γ st) ∗
    ([∗list] p ∈ s.rd.pend, ∃ e c Lc, ⌜p.2 = [e]⌝ ∗ isPropData γ e.Data' c ∗ readReq γ c Lc) ∗
    rdCred γ (s.rd.pend.length + rdCount s.outbox) ∗
    rdCredInv γ)

/-- Across a step that touches no read state: a leader stays one only within its term and
read state, a non-leader's read-only object is the fresh one, a leader leaves its term only
for a higher one, the `ReadState`s and pending requests are kept, and the outbox holds no
more read-index requests. -/
theorem rdOwn_mono (γ : RaftNames) (id : w64) (s s' : PState) :
    (s'.role = .leader → s.role = .leader ∧ s'.term = s.term ∧ s'.rd = s.rd) →
    (s'.role ≠ .leader →
       s'.rd.ro = ⟨[], ∅, W64 0⟩ ∨ (s.role ≠ .leader ∧ s'.rd.ro = s.rd.ro)) →
    (s'.role ≠ .leader → s.role = .leader → uint.Z s.term < uint.Z s'.term) →
    uint.Z s.term ≤ uint.Z s'.term →
    s'.rd.states = s.rd.states → s'.rd.pend = s.rd.pend →
    rdCount s'.outbox ≤ rdCount s.outbox →
    rdOwn (GF := GF) γ id s ⊢ rdOwn γ id s' := by
  intro Hlead Hnl Hdown Hle Hst Hpd Hcnt
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, Hl, #Hst0, #Hpd0, Hcr, #Hinv⟩
  iexists γl, rqm
  iframe Ha Hf Hinv
  isplitr; · ipureintro; exact Hγl
  isplitr
  · ipureintro
    intro t Ht
    rcases Hok t Ht with Hlt | ⟨rfl, Hr⟩
    · left; omega
    · by_cases Hr' : s'.role = .leader
      · obtain ⟨-, Hte, -⟩ := Hlead Hr'; right; exact ⟨Hte.symm, Hr'⟩
      · left; exact Hdown Hr' Hr
  isplitl [Hl]
  · by_cases Hr' : s'.role = .leader
    · obtain ⟨Hr, Hte, Hrd⟩ := Hlead Hr'
      unfold rdLead; rw [Hr, Hr', Hte, Hrd]
      iexact Hl
    · rw [rdLead_nl γ s' rqm Hr']
      rcases Hnl Hr' with H | ⟨Hr, H⟩
      · ipureintro; exact H
      · rw [rdLead_nl γ s rqm Hr]
        icases Hl with %H0
        ipureintro; rw [H]; exact H0
  rw [Hst, Hpd]
  iframe Hst0 Hpd0
  ihave Hcr := (rdCred_split γ (s.rd.pend.length + rdCount s'.outbox)
    (rdCount s.outbox - rdCount s'.outbox)).1 $$ [Hcr]
  · rw [show s.rd.pend.length + rdCount s'.outbox + (rdCount s.outbox - rdCount s'.outbox)
      = s.rd.pend.length + rdCount s.outbox by omega]
    iexact Hcr
  icases Hcr with ⟨Hcr, -⟩
  iexact Hcr

/-- Winning: a registry for the term, empty, the read-only object fresh. -/
theorem rdOwn_win (γ : RaftNames) (id : w64) (s s' : PState) :
    s.role ≠ .leader → s'.role = .leader → s'.term = s.term →
    s'.rd = rdNL s.rd → rdCount s'.outbox ≤ rdCount s.outbox →
    rdOwn (GF := GF) γ id s ⊢ |==> rdOwn γ id s' := by
  intro Hr Hr' Hte Hrd Hcnt
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, -, #Hst0, #Hpd0, Hcr, #Hinv⟩
  have Hfree : rqm !! s.term = none := by
    cases h : rqm !! s.term with
    | none => rfl
    | some _ =>
      rcases Hok s.term (by simp [h]) with Hlt | ⟨-, Hl⟩
      · omega
      · exact absurd Hl Hr
  imod mono_list_own_alloc (GF := GF) ([] : List RqRec) with ⟨%γq, Haq, -⟩
  imod ghost_map_insert_persist s.term γq Hfree $$ Ha with ⟨Ha, #Hfq⟩
  have Hpd : s'.rd.pend = s.rd.pend := by rw [Hrd]; rfl
  have Hst : s'.rd.states = s.rd.states := by rw [Hrd]; rfl
  ihave Hcr := (rdCred_split γ (s'.rd.pend.length + rdCount s'.outbox)
    (rdCount s.outbox - rdCount s'.outbox)).1 $$ [Hcr]
  · rw [Hpd, show s.rd.pend.length + rdCount s'.outbox + (rdCount s.outbox - rdCount s'.outbox)
      = s.rd.pend.length + rdCount s.outbox by omega]
    iexact Hcr
  icases Hcr with ⟨Hcr, Hcr0⟩
  ihave Hcr0 := (rdCred_split γ 0 (rdCount s.outbox - rdCount s'.outbox)).1 $$ [Hcr0]
  · rw [Nat.zero_add]; iexact Hcr0
  icases Hcr0 with ⟨Hz, -⟩
  imodintro
  iexists γl, (<[s.term := γq]> rqm)
  iframe Ha Hinv Hcr
  isplitr; · ipureintro; exact Hγl
  isplitr
  · iapply (BigSepM.bigSepM_insert (Φ := fun t γc => iprop(t ↪[γl]□ γc)) Hfree).2
    isplitr; · iexact Hfq
    iexact Hf
  isplitr
  · ipureintro
    intro t Ht
    by_cases Htt : s.term = t
    · subst Htt; right; exact ⟨Hte.symm, Hr'⟩
    · rw [GMap.lookup_insert_ne _ _ Htt] at Ht
      rcases Hok t Ht with Hlt | ⟨rfl, Hl⟩
      · left; rw [Hte]; exact Hlt
      · exact absurd Hl Hr
  isplitl [Haq Hz]
  · unfold rdLead
    rw [Hr']
    iexists γq, []
    isplitr
    · ipureintro; rw [Hte]; simp
    iframe Haq
    have Hro : s'.rd.ro = ⟨[], ∅, W64 0⟩ := by rw [Hrd]; rfl
    rw [Hro]
    isplitr; · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr; · ipureintro; rfl
    isplitr; · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · ipureintro; intro v a h; simp at h
    · iexact Hz
  rw [Hst, Hpd]
  iframe Hst0 Hpd0

/-- The `ReadState`s handed out: each `readStateOk`, and the rest unchanged. -/
theorem rdOwn_takeReads (γ : RaftNames) (id : w64) (s : PState) :
    rdOwn (GF := GF) γ id s ⊢
      rdOwn γ id { s with rd := { s.rd with states := [] } } ∗
      [∗list] st ∈ s.rd.states, readStateOk γ st := by
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, Hl, #Hst0, #Hpd0, Hcr, #Hinv⟩
  isplitl [Ha Hl Hcr]
  · iexists γl, rqm
    isplitr; · ipureintro; exact Hγl
    isplitl [Ha]; · iexact Ha
    isplitr; · iexact Hf
    isplitr; · ipureintro; exact Hok
    isplitl [Hl]
    · rw [show rdLead (GF := GF) γ { s with rd := { s.rd with states := [] } } rqm =
        rdLead γ s rqm from rfl]
      iexact Hl
    isplitr; · iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr; · iexact Hpd0
    isplitl [Hcr]; · iexact Hcr
    iexact Hinv
  · iexact Hst0

/-- A step that changes only the outbox and the read state, not the read-only object:
`ReadState`s added, pending requests added (each with its facts and a credit), and
messages sent with as many credits as they hold read-index requests. -/
theorem rdOwn_update (γ : RaftNames) (id : w64) (s s' : PState) (sts : List ReadState)
    (ps : List (raftpb.Message × List raftpb.Entry)) (ms : List Msg) :
    s'.role = s.role → s'.term = s.term → s'.rd.ro = s.rd.ro →
    s'.rd.states = s.rd.states ++ sts → s'.rd.pend = s.rd.pend ++ ps →
    s'.outbox = s.outbox ++ ms →
    ⊢ rdOwn (GF := GF) γ id s -∗ ([∗list] st ∈ sts, readStateOk γ st) -∗
      ([∗list] p ∈ ps, ∃ e c Lc, ⌜p.2 = [e]⌝ ∗ isPropData γ e.Data' c ∗ readReq γ c Lc) -∗
      rdCred γ (ps.length + rdCount ms) -∗
      rdOwn γ id s' := by
  intro Hr Ht Hro Hst Hpd Hout
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, Hl, #Hst0, #Hpd0, Hcr, #Hinv⟩ #Hsts #Hps Hcr'
  iexists γl, rqm
  isplitr; · ipureintro; exact Hγl
  isplitl [Ha]; · iexact Ha
  isplitr; · iexact Hf
  isplitr
  · ipureintro
    intro t Htt
    rw [Ht, Hr]; exact Hok t Htt
  isplitl [Hl]
  · have : rdLead (GF := GF) γ s' rqm = rdLead γ s rqm := by
      unfold rdLead; rw [Hr, Ht, Hro]
    rw [this]; iexact Hl
  isplitr
  · rw [Hst]
    iapply (BigSepL.bigSepL_append (Φ := fun _ st => readStateOk (GF := GF) γ st)).2
    iframe Hst0 Hsts
  isplitr
  · rw [Hpd]
    iapply (BigSepL.bigSepL_append (Φ := fun _ (p : raftpb.Message × List raftpb.Entry) => iprop(∃ e c Lc, ⌜p.2 = [e]⌝ ∗
      isPropData (GF := GF) γ e.Data' c ∗ readReq γ c Lc))).2
    iframe Hpd0 Hps
  isplitl [Hcr Hcr']
  · rw [Hpd, Hout, List.length_append, rdCount_append,
      show s.rd.pend.length + ps.length + (rdCount s.outbox + rdCount ms) =
        (s.rd.pend.length + rdCount s.outbox) + (ps.length + rdCount ms) by omega]
    iapply (rdCred_split γ _ _).2
    iframe Hcr Hcr'
  iexact Hinv

/-- Messages leaving the outbox (`Ready`): their read credits go with them. -/
theorem rdOwn_drain (γ : RaftNames) (id : w64) (s : PState) (o' : List Msg)
    (h : rdCount o' ≤ rdCount s.outbox) :
    rdOwn (GF := GF) γ id s ⊢
      rdOwn γ id { s with outbox := o' } ∗ rdCred γ (rdCount s.outbox - rdCount o') := by
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, Hl, #Hst0, #Hpd0, Hcr, #Hinv⟩
  rw [show s.rd.pend.length + rdCount s.outbox =
      (s.rd.pend.length + rdCount o') + (rdCount s.outbox - rdCount o') by omega]
  icases (rdCred_split γ _ _).1 $$ Hcr with ⟨Hc1, Hc2⟩
  iframe Hc2
  iexists γl, rqm
  isplitr; · ipureintro; exact Hγl
  isplitl [Ha]; · iexact Ha
  isplitr; · iexact Hf
  isplitr; · ipureintro; exact Hok
  isplitl [Hl]
  · rw [show rdLead (GF := GF) γ { s with outbox := o' } rqm = rdLead γ s rqm from rfl]
    iexact Hl
  isplitr; · iexact Hst0
  isplitr; · iexact Hpd0
  isplitl [Hc1]; · iexact Hc1
  iexact Hinv

/-- The pending requests taken out, with their facts and credits. -/
theorem rdOwn_takePend (γ : RaftNames) (id : w64) (s : PState) :
    rdOwn (GF := GF) γ id s ⊢
      rdOwn γ id { s with rd := { s.rd with pend := [] } } ∗
      ([∗list] p ∈ s.rd.pend, ∃ e c Lc, ⌜p.2 = [e]⌝ ∗ isPropData γ e.Data' c ∗ readReq γ c Lc) ∗
      rdCred γ s.rd.pend.length := by
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, Hl, #Hst0, #Hpd0, Hcr, #Hinv⟩
  icases (rdCred_split γ s.rd.pend.length (rdCount s.outbox)).1 $$ Hcr with ⟨Hc1, Hc2⟩
  iframe Hpd0 Hc1
  iexists γl, rqm
  isplitr; · ipureintro; exact Hγl
  isplitl [Ha]; · iexact Ha
  isplitr; · iexact Hf
  isplitr; · ipureintro; exact Hok
  isplitl [Hl]
  · rw [show rdLead (GF := GF) γ { s with rd := { s.rd with pend := [] } } rqm =
      rdLead γ s rqm from rfl]
    iexact Hl
  isplitr; · iexact Hst0
  isplitr; · iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitl [Hc2]
  · rw [show ({ s with rd := { s.rd with pend := [] } } : PState).rd.pend.length +
        rdCount ({ s with rd := { s.rd with pend := [] } } : PState).outbox = rdCount s.outbox
      by simp]
    iexact Hc2
  iexact Hinv

/-- What the read-index code needs of a leader's read-only state (2026-10-13; `RdOk`):
its acknowledgements are positions its queue reaches, its requests and pending ones have
entries. -/
theorem rdOwn_rdFacts (γ : RaftNames) (id : w64) (s : PState) (Hr : s.role = .leader) :
    ⊢ rdOwn (GF := GF) γ id s -∗
      ⌜(∀ v a, s.rd.ro.acks !! v = some a →
          uint.nat a ≤ uint.nat s.rd.ro.confirmed + s.rd.ro.pending.length) ∧
        (∀ q ∈ s.rd.ro.pending, q.ents ≠ []) ∧ (∀ p ∈ s.rd.pend, p.2 ≠ [])⌝ := by
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, -, -, -, Hl, -, #Hpd0, -⟩
  unfold rdLead
  rw [Hr]
  icases Hl with ⟨%γq, %recs, %Hq, -, -, %Hlen, #Hpq, %Hacks, -⟩
  ihave Hp1 : ([∗list] k ↦ x ∈ s.rd.ro.pending, ⌜x.ents ≠ []⌝ : IProp GF) $$ []
  · iapply BigSepL.bigSepL_impl $$ Hpq
    imodintro
    iintro %k %x %Hk ⟨%r, %e, %H, -⟩
    ipureintro
    rw [H.2.2]; exact List.cons_ne_nil _ _
  ihave %Hp1' := BigSepL.bigSepL_pure_intro $$ Hp1
  ihave Hp2 : ([∗list] k ↦ x ∈ s.rd.pend, ⌜x.2 ≠ []⌝ : IProp GF) $$ []
  · iapply BigSepL.bigSepL_impl $$ Hpd0
    imodintro
    iintro %k %x %Hk ⟨%e, %c, %Lc, %H, -⟩
    ipureintro
    rw [H]; exact List.cons_ne_nil _ _
  ihave %Hp2' := BigSepL.bigSepL_pure_intro $$ Hp2
  ipureintro
  refine ⟨fun v a h => ?_, fun q hq => ?_, fun p hp => ?_⟩
  · have := (Hacks v a h).1; omega
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq; exact Hp1' k q hk
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp; exact Hp2' k p hk

/-- A heartbeat response's position, at the leader of its term: at most its queue's end. -/
theorem rdOwn_hbResp_pos (γ : RaftNames) (id : w64) (s : PState) (Hr : s.role = .leader)
    (recs0 : List RqRec) (q : w64) (Hq : uint.nat q ≤ recs0.length) :
    ⊢ rdOwn (GF := GF) γ id s -∗ rqLb γ id s.term recs0 -∗
      ⌜uint.nat q ≤ uint.nat s.rd.ro.confirmed + s.rd.ro.pending.length⌝ := by
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, Ha, -, -, Hl, -⟩ #Hlb
  unfold rdLead
  rw [Hr]
  icases Hl with ⟨%γq, %recs, %Hq', Hauth, -, %Hlen, -⟩
  unfold rqLb
  icases Hlb with ⟨%γl', %γq'', %Hγl', #Hel, #Hlb⟩
  rw [Hγl] at Hγl'
  cases Hγl'
  icases ghost_map_lookup $$ Ha Hel with %Hq2
  have Hqq : γq = γq'' := by
    have h1 : rqm !! s.term = some γq'' := Hq2
    rw [Hq'] at h1
    exact Option.some.inj h1
  subst Hqq
  icases mono_list_auth_lb_valid $$ Hauth Hlb with %Hpre
  ipureintro
  have := Hpre.2.length_le
  omega

/-- A leader's registry, at least up to the end of its queue. -/
theorem rdOwn_regLb (γ : RaftNames) (id : w64) (s : PState) (Hr : s.role = .leader) :
    ⊢ rdOwn (GF := GF) γ id s -∗
      ∃ (recs : List RqRec), ⌜recs.length = uint.nat s.rd.ro.confirmed + s.rd.ro.pending.length⌝ ∗
        rqLb γ id s.term recs ∗ [∗list] r ∈ recs, rqRecOk γ s.term r := by
  unfold rdOwn
  iintro ⟨%γl, %rqm, %Hγl, -, #Hf, -, Hl, -⟩
  unfold rdLead
  rw [Hr]
  icases Hl with ⟨%γq, %recs, %Hq, Ha, #Hrs, %Hlen, -⟩
  iexists recs
  ihave #Hlb := monoListLbOwn_get $$ Ha
  ihave #Ht := BigSepM.bigSepM_lookup (Φ := fun t γq => iprop(t ↪[γl]□ γq)) Hq $$ Hf
  isplitr; · ipureintro; exact Hlen
  isplitr
  · unfold rqLb
    iexists γl, γq
    isplitr
    · ipureintro; exact Hγl
    iframe Ht Hlb
  · iexact Hrs

/-- What a heartbeat of an allowed context carries. -/
theorem hbCtx_isMessage (γ : RaftNames) (id T : w64) (r : ReadOnly) (ctx : List w8)
    (recs : List RqRec) :
    HbCtxOk r ctx → recs.length = uint.nat r.confirmed + r.pending.length →
    ⊢ rqLb (GF := GF) γ id T recs -∗ ([∗list] x ∈ recs, rqRecOk γ T x) -∗
      (⌜ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜ctx = u64Le q ∧ uint.nat q ≤ recs.length⌝ ∗ rqLb γ id T recs ∗
         [∗list] x ∈ recs, rqRecOk γ T x) := by
  intro Hc Hlen
  iintro #Hlb #Hrs
  rcases Hc with H0 | ⟨q, Hq, Hle⟩
  · ileft; ipureintro; exact H0
  · iright
    iexists q, recs
    iframe Hlb Hrs
    ipureintro; exact ⟨Hq, by omega⟩

/-- The terms a node has won: as `TermsOk`. -/
def WinsOk (wins : GMap w64 (GSet w64)) (s : PState) : Prop :=
  ∀ t, (wins !! t).isSome →
    uint.Z t < uint.Z s.term ∨
    (t = s.term ∧ s.role = .leader)

def ownLogGhost (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) : IProp GF :=
  iprop(∃ γm, ∃ (terms : GMap w64 TermRec), ∃ γa, ∃ (acks : GMap (w64 × w64) Unit),
    ∃ (fp : List raftpb.Entry), ∃ γc, ∃ (camps : GMap w64 (List raftpb.Entry × w64)), ∃ γl,
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

def ownRaftGhost (γ : RaftNames) (id : w64) (s : PState) (md : Bool := false) : IProp GF :=
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
    "%Hrole_ok" ∷ ⌜RoleOk id s⌝ ∗
    -- 2026-10-12 (read-index): the commit lower bounds of the terms it led
    "Hlcm"     ∷ lcmOwn γ id s ∗
    -- 2026-10-12: the read-index ghost state
    "Hrd"      ∷ rdOwn γ id s ∗
    -- 2026-10-14 (reconfiguration stage B5): the mode, `md` (`false` by default: the code's
    -- ghost state is static, `γ.reDyn = none`, `ownRaftGhost_static`)
    "%Hmode"   ∷ ⌜γ.reDyn.isSome = md⌝)

-- Not `Timeless` since 2026-10-05: `ownLogGhost` holds the invariant `raftCommitInv`.

theorem ownRaftGhost_intro (γ : RaftNames) (id : w64) (s : PState) (γv : GName)
    (voted : GMap w64 w64) (kl : Option w64) {md : Bool} :
    γ.reVotes !! id = some γv →
    id ≠ W64 0 →
    γ.reDyn.isSome = md →
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
      lcmOwn γ id s -∗
      rdOwn γ id s -∗
      ownRaftGhost γ id s md := by
  intro Hname Hidnz Hmode
  unfold ownRaftGhost
  iintro H1 %H2 #H3 #H4 #H5 #H6 H7 %H8 %H9 #H10 %H11 H12 H13
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
  isplitr; · ipureintro; exact H11
  isplitl [H12]; · iexact H12
  isplitl [H13]; · iexact H13
  ipureintro; exact Hmode

/-- The mode of a node's ghost state. -/
theorem ownRaftGhost_mode (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ⌜γ.reDyn.isSome = md⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hmode

/-- The code's ghost state is static. -/
theorem ownRaftGhost_static (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ ⌜γ.reDyn = none⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro
  cases h : γ.reDyn with
  | none => rfl
  | some _ => rw [h] at Hmode; cases Hmode

/-- A non-leader does not record itself as leader. -/
theorem ownRaftGhost_lead_ok (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ⌜LeadOk id s⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hlead_ok

/-- A follower's tally is empty. -/
theorem ownRaftGhost_follower_votes (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ⌜FollowerVotesOk s⌝ := by
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
    ⊢ ownRaftGhost (GF := GF) γ id s1 md -∗ ownRaftGhost γ id s2 md -∗ False := by
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
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ([∗list] m ∈ s.outbox, isMessage γ m) := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iexact Hout

theorem ownRaftGhost_isLeader (γ : RaftNames) (id : w64) (s : PState) :
    s.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ isLeader γ id s.term := by
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
