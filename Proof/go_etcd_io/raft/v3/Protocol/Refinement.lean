/-
Port of election_proof/protocol.v, lines 4495–6250 at feb5c73d4: the refinement
obligation one rule at a time, and the refinement obligation `ownRaftGhost_step`. (On
top of `Protocol/LeaderCompleteness.lean`; the protocol facts the code needs are
`Protocol/Facts.lean`.)

Lean notes:
* All proofs are filled in. The helper lemmas they use (Lean additions, all `private`:
  big-op and message plumbing, `ownRaftGhost_step_stale` for `Step.appStale`/`Step.snapStale`,
  `logRecs_intro`/`logRecs_elem`, the `…_leader`/`…_cand` unfoldings of role-indexed
  definitions) are between the `BEGIN/END HELPERS` markers before `ownRaftGhost_step_win`.
* `own_raft_ghost_step_<rule>` is `ownRaftGhost_step_<rule>` (the rule part kept in
  Rocq's snake_case: `ownRaftGhost_step_app_accept`). Rocq `Local Lemma`s are public.
* `Forall P ms` is `∀ m ∈ ms, P m`; `s <| f := v |>` is `{ s with f := v }`; `imap` is
  `List.mapIdx`; `if decide P then` is `if P then`. Rocq's `let s' := … in` in
  `own_raft_ghost_step_propose`'s statement is inlined (as `Model.lean` does in
  `Step.propose`).
* The Rocq `Local Ltac`s `destruct_ghost`, `role_ok_tac`, `lead_ok_tac`,
  `follower_votes_tac` (proof automation) are kept as comments; they are not ported as
  macros (the proofs discharge those side conditions inline).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.ReadIndex

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

set_option hygiene false in
/-- The commit lower bounds across a rule that neither makes a leader nor moves a leader's
term (2026-10-12, `lcmOwn_mono`): each of the four premises is a computation on the
rule's states. -/
local macro "lcm_mono" : tactic => `(tactic| (
  iapply lcmOwn_mono _ _ _ _ ?_ ?_ ?_ ?_ $$ Hlcm <;>
  first
    | (intro h; simp_all [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; done)
    | (intro h h'; simp_all [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; done)
    | (simp_all [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; done)
    | (simp [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; omega)
    | (simp [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate, plogCommitTo];
       split <;> omega)
    | (intro h; exact absurd h (by simp_all))
    | (simp_all; done)
    | exact Int.le_refl _
    | omega
    | (dsimp only [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; omega)
    | (intro _ _; dsimp only [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; omega)
    | word))

set_option hygiene false in
/-- The read-index ghost state across a rule that touches no read state (2026-10-12,
`rdOwn_mono`). -/
local macro "rd_mono" : tactic => `(tactic| (
  iapply rdOwn_mono _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $$ Hrd <;>
  first
    | rfl
    | (intro h; right; exact ⟨by assumption, rfl⟩)
    | (intro h; left; rfl)
    | (apply List.Subperm.countP_le; assumption)
    | (intro h; simp_all [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate, rdNL]; done)
    | (intro h; right; exact ⟨by simp_all, rfl⟩)
    | (intro h; left; simp [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate, rdNL])
    | (intro h h'; simp_all [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; done)
    | (intro h h'; dsimp only [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; omega)
    | (simp_all [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate, rdNL]; done)
    | (simp [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; omega)
    | (dsimp only [psendMsgs, padoptLeader, pbecomeFollower, pbecomeCandidate]; omega)
    | (simp_all [rdCount_append, psendMsgs]; done)
    | (simp [rdCount, psendMsgs, List.countP_append, List.countP_map, pvoteReq, Msg.plain,
        Function.comp_def]; done)
    | (simp [rdCount_append, rdCount_singleton, psendMsgs, Msg.plain]; done)
    | (simp_all [rdCount_append, rdCount_singleton, psendMsgs, pselfAck]; done)
    | (simp [rdCount, psendMsgs, List.countP_append]; done)
    | (simp [rdCount, psendMsgs, List.countP_append, List.countP_cons, List.countP_nil]; omega)
    | exact Int.le_refl _
    | exact Nat.le_refl _
    | omega
    | word))

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

theorem rdCount_replOk (id : w64) (s : PState) (ms : List Msg) (h : ∀ m ∈ ms, ReplOk id s m) :
    rdCount ms = 0 := by
  unfold rdCount; rw [List.countP_eq_zero]
  intro m hm
  rcases h m hm with h' | h' <;> simp [h'.1]


/-! ### The refinement obligation, one rule at a time

The election rules are proved inline in `ownRaftGhost_step`; the replication rules each
have a lemma here. -/

/- Rocq:
```
Local Ltac destruct_ghost :=
  iDestruct "Hown" as (γv voted kl)
    "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead & Hlg & %Hlok & %Hfv & #Hvrecs & %Hrok)".
```
`RoleOk` of the state a rule produces: unchanged role, vote and leader, or a follower.
```
Local Ltac role_ok_tac :=
  first
    [ assumption
    | let H1 := fresh in let H2 := fresh in
      match goal with H : role_ok _ _ |- _ => pose proof H as [H1 H2] end;
      rewrite /role_ok /psend_msgs /padopt_leader /pbecome_follower /=; split; intros ?;
      first [ congruence | done | by apply H1 | by apply H2 ] ].
```
`LeadOk` of the state a rule produces: unchanged role and leader, or a leader, or a
follower with no leader / another node as leader.
```
Local Ltac lead_ok_tac :=
  first
    [ assumption
    | rewrite /lead_ok /=; intros Hr;
      first [ by exfalso; apply Hr | assumption | congruence ] ].
```
`FollowerVotesOk` of the state a rule produces, likewise.
```
Local Ltac follower_votes_tac :=
  first
    [ assumption
    | rewrite /follower_votes_ok /=; intros Hr; first [ done | congruence ] ].
```
-/

/-! ### Helpers (Lean additions) -/
-- BEGIN HELPERS (Lean addition)
private theorem outbox_app (γ : RaftNames) (o ms : List Msg) :
    ⊢ ([∗list] m ∈ o, isMessage (GF := GF) γ m) -∗ ([∗list] m ∈ ms, isMessage γ m) -∗
      [∗list] m ∈ o ++ ms, isMessage γ m := by
  iintro Ho Hms
  iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  isplitl [Ho]
  · iexact Ho
  · iexact Hms

private theorem outbox_snoc (γ : RaftNames) (o : List Msg) (m : Msg) :
    ⊢ ([∗list] m ∈ o, isMessage (GF := GF) γ m) -∗ isMessage γ m -∗
      [∗list] m ∈ o ++ [m], isMessage γ m := by
  iintro Ho Hm
  iapply outbox_app $$ Ho
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  iexact Hm

private theorem leaderWit_eq (γ : RaftNames) (id : w64) (s1 s2 : PState) :
    s2.role = s1.role → s2.term = s1.term →
    ⊢ leaderWit (GF := GF) γ id s1 -∗ leaderWit γ id s2 := by
  intro H1 H2
  unfold leaderWit; rw [H1, H2]
  iintro H; iexact H

private theorem leaderWit_nonleader (γ : RaftNames) (id : w64) (s : PState) :
    s.role ≠ .leader → ⊢ leaderWit (GF := GF) γ id s := by
  intro H
  unfold leaderWit
  split
  · exact absurd ‹_› H
  · exact true_intro

private theorem tally_eq (γ : RaftNames) (id : w64) (s1 s2 : PState) :
    s2.votes = s1.votes → s2.term = s1.term →
    ⊢ ([∗map] v ↦ _u ∈ toMap (granted s1.votes), isVote (GF := GF) γ v s1.term id) -∗
      [∗map] v ↦ _u ∈ toMap (granted s2.votes), isVote γ v s2.term id := by
  intro H1 H2
  rw [H1, H2]
  iintro H; iexact H

private theorem tally_empty (γ : RaftNames) (id : w64) (s : PState) :
    s.votes = ∅ →
    ⊢ [∗map] v ↦ _u ∈ toMap (granted s.votes), isVote (GF := GF) γ v s.term id := by
  intro H
  rw [H, granted_empty]
  exact BigSepM.bigSepM_empty.2

/-- What `lpfull` says of the compacted prefix. -/
private theorem lpfull_fp (γ : RaftNames) (ldr t : w64) (bL : entryID)
    (l fp : List raftpb.Entry) :
    ⊢ lpfull (GF := GF) γ ldr t bL l fp -∗
      logRecs γ base0 fp ∗
      ⌜FullOk bL fp ∧ PlogWf bL l ∧
        ∀ (j x : w64), plogTermAt base0 (fp ++ l) j = some x → uint.Z x ≤ uint.Z t⌝ := by
  unfold lpfull
  iintro ⟨%F0, -, #Hr, %H⟩
  isplitr
  · iexact Hr
  · ipureintro; exact ⟨H.1, H.2.2.1, H.2.2.2⟩

private theorem isMessage_appResp_inv (γ : RaftNames) (m : Msg) :
    m.ty = .appResp → m.reject = false →
    ⊢ isMessage (GF := GF) γ m -∗ isAcked γ m.src m.term m.index := by
  intro Hty Hrej
  unfold isMessage; rw [Hty]; simp only [Hrej, Bool.false_eq_true, ↓reduceIte]
  iintro H; iexact H

private theorem isMessage_appResp (γ : RaftNames) (src dst term idx : w64) :
    ⊢ isAcked (GF := GF) γ src term idx -∗
      isMessage γ (Msg.mk .appResp src dst term false idx (W64 0) (W64 0) (W64 0) []) := by
  unfold isMessage
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro H; iexact H

private theorem isMessage_appResp_rej (γ : RaftNames) (src dst term idx a b c : w64) :
    ⊢ isMessage (GF := GF) γ (Msg.mk .appResp src dst term true idx a b c []) := by
  unfold isMessage; simp only [↓reduceIte]; exact true_intro

private theorem matchedOk_leader (γ : RaftNames) (s : PState) :
    s.role = .leader →
    matchedOk (GF := GF) γ s = iprop([∗map] v ↦ i ∈ s.matched, isAcked γ v s.term i) := by
  intro H; unfold matchedOk; rw [H]

private theorem isMessage_app_inv (γ : RaftNames) (m : Msg) :
    m.ty = .app →
    ⊢ isMessage (GF := GF) γ m -∗
      ⌜AppPayloadOk m⌝ ∗
      isLeader γ m.src m.term ∗
      (∃ bL l fp, leadPrefix γ m.src m.term bL l ∗
         ⌜plogTermAt bL l m.index = some m.logterm ∧
           m.entries <+: plogFrom bL l (m.index + W64 1)⌝ ∗
         lpfull γ m.src m.term bL l fp ∗
         commitIn γ (fp ++ l) m.commit m.term ∗
         isCommitted γ ((fp ++ l).take (uint.Z m.commit).toNat)) ∗
      ⌜m.src ≠ W64 0⌝ := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

private theorem isMessage_heartbeat_inv (γ : RaftNames) (m : Msg) :
    m.ty = .heartbeat →
    ⊢ isMessage (GF := GF) γ m -∗
      isLeader γ m.src m.term ∗
      (∃ Fl, leadFull γ m.term Fl ∗ commitIn γ Fl m.commit m.term ∗
         isCommitted γ (Fl.take (uint.Z m.commit).toNat)) ∗
      (∃ i, ⌜uint.Z m.commit ≤ uint.Z i⌝ ∗ isAcked γ m.dst m.term i) ∗
      ⌜m.src ≠ W64 0⌝ ∗
      (⌜m.ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜m.ctx = u64Le q ∧ uint.nat q ≤ recs.length⌝ ∗ rqLb γ m.src m.term recs ∗
         [∗list] r ∈ recs, rqRecOk γ m.term r) := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

private theorem isMessage_snap_inv (γ : RaftNames) (m : Msg) :
    m.ty = .snap →
    ⊢ isMessage (GF := GF) γ m -∗
      isLeader γ m.src m.term ∗
      isSnapMeta γ m.logterm m.index ∗
      (∃ bL l fp, leadPrefix γ m.src m.term bL l ∗
         ⌜plogTermAt bL l m.index = some m.logterm⌝ ∗
         lpfull γ m.src m.term bL l fp ∗
         commitIn γ (fp ++ l) m.index m.term ∗
         isCommitted γ ((fp ++ l).take (uint.Z m.index).toNat)) ∗
      ⌜m.src ≠ W64 0⌝ := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

/-- What the leader-adopting rules share: the sender is the leader of the term. -/
private theorem isMessage_leader (γ : RaftNames) (m : Msg) :
    m.ty = .app ∨ m.ty = .heartbeat ∨ m.ty = .snap →
    ⊢ isMessage (GF := GF) γ m -∗ isLeader γ m.src m.term ∗ ⌜m.src ≠ W64 0⌝ := by
  intro Hty
  iintro #Hm
  rcases Hty with Hty | Hty | Hty
  · icases isMessage_app_inv γ m Hty $$ Hm with ⟨-, #Hl, -, %Hnz⟩
    isplitr
    · iexact Hl
    · ipureintro; exact Hnz
  · icases isMessage_heartbeat_inv γ m Hty $$ Hm with ⟨#Hl, -, -, %Hnz, -⟩
    isplitr
    · iexact Hl
    · ipureintro; exact Hnz
  · icases isMessage_snap_inv γ m Hty $$ Hm with ⟨#Hl, -, -, %Hnz⟩
    isplitr
    · iexact Hl
    · ipureintro; exact Hnz

/-- `Step.appStale` and `Step.snapStale`: learn the leader, adopt it, and acknowledge the
commit index. -/
private theorem ownRaftGhost_step_stale (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    (m.ty = .app ∨ m.ty = .snap) →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) := by
  intro Hty Hfid Hterm Hrole
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases isMessage_leader γ m (by rcases Hty with h | h <;> simp [h]) $$ Hm with ⟨#Hl, %Hfnz⟩
  rw [Hterm]
  iunfold isLeader at Hl
  icases Hl with ⟨%q, #Hwin⟩
  ihave %Hex := vote_excl γ id s γv voted m.src q Hname Hhist $$ Hvoted Hwin
  ihave Hlg := ownLogGhost_learn γ id s kl m.src q Hrole $$ Hwin %Hex Hlg
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  ihave Hlg := ownLogGhost_mono γ id s (padoptLeader s m.src) (some m.src) rfl rfl rfl
    (by intro h; cases h) (by intro h; cases h) (by intro h; exact absurd h Hrole) rfl (fun h => h) $$ Hlg
  imod ownLogGhost_ack γ id (padoptLeader s m.src) (some m.src) s.commit $$ [] [] Hlg with ⟨Hlg, #Hack⟩
  · unfold ackOk
    iintro %H
    exfalso; exact absurd H.2 (Int.lt_irrefl _)
  · iintro %fp % ⟨Hf, Hw⟩ #Hfr #Hc
    simp only [padoptLeader] at Hf Hw ⊢
    iapply hist_of_commit γ _ _ _ _ (full_wf _ _ _ Hf Hw)
      (by show uint.Z s.term < uint.Z s.term + 1; omega) $$ [] Hc
    iapply logRecs_full γ s.base fp s.log Hf $$ Hfr Hrecs
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted (some m.src) Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]; simp only [padoptLeader]
    iapply outbox_snoc $$ Hout
    iapply isMessage_appResp $$ Hack
  · iapply tally_empty γ id _ (by rfl)
  · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
  · iapply ownLogGhost_mono γ id (padoptLeader s m.src) _ (some m.src) (by rfl) (by rfl) (by rfl)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by rfl) (by exact fun h => h)
      $$ Hlg
  · ipureintro; intro _; exact Hfid
  · ipureintro; intro _; rfl
  · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
  · lcm_mono
  · rd_mono

private theorem matchedOk_nonleader (γ : RaftNames) (s : PState) :
    s.role ≠ .leader → ⊢ matchedOk (GF := GF) γ s := by
  intro H
  unfold matchedOk
  split
  · exact absurd ‹_› H
  · exact true_intro

private theorem cq_term (γ : RaftNames) (t n : w64) (G : List raftpb.Entry) :
    ⊢ cq (GF := GF) γ t n G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  unfold cq
  iintro ⟨%H, -⟩
  ipureintro; exact H

private theorem plogCommitTo_ge (c t : w64) : uint.Z c ≤ uint.Z (plogCommitTo c t) := by
  unfold plogCommitTo; split <;> omega
private theorem outbox_eq (γ : RaftNames) (s1 s2 : PState) :
    s2.outbox = s1.outbox →
    ⊢ ([∗list] m ∈ s1.outbox, isMessage (GF := GF) γ m) -∗ [∗list] m ∈ s2.outbox, isMessage γ m := by
  intro H; rw [H]; iintro H; iexact H

private theorem isMessage_vote_inv (γ : RaftNames) (m : Msg) :
    m.ty = .vote →
    ⊢ isMessage (GF := GF) γ m -∗
      ∃ Fc, isCamp γ m.src m.term Fc ∗ ⌜plogLast base0 Fc = entryID.mk m.logterm m.index⌝ := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

private theorem isMessage_voteReq (γ : RaftNames) (id dst t : w64) (last : entryID)
    (F : List raftpb.Entry) :
    plogLast base0 F = last →
    ⊢ isCamp (GF := GF) γ id t F -∗ isMessage γ (pvoteReq id dst t last) := by
  intro H
  unfold isMessage pvoteReq
  dsimp only
  iintro #Hc
  iexists F
  iframe Hc
  ipureintro; rw [H]

/-- The received message of a one-message rule. -/
private theorem recv_one (γ : RaftNames) (m : Msg) :
    ⊢ ([∗list] m ∈ [m], isMessage (GF := GF) γ m) -∗ isMessage γ m := by
  iintro H
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ H
private theorem logRecs_intro (γ : RaftNames) (b : entryID) (es : List raftpb.Entry) :
    ⊢ □ (∀ (k : Nat) (x : raftpb.Entry),
          ⌜es[k]? = some x ∧ uint.Z b.index' + (k : Int) + 1 < 2 ^ 64⌝ →
          ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ x pt) -∗
      logRecs γ b es := by
  iintro #H
  unfold logRecs
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %x Hk
  ipure Hk
  split
  · rename_i Hr
    iapply H $$ %k %x
    ipureintro; exact ⟨Hk, Hr⟩
  · itrivial

private theorem logRecs_elem (γ : RaftNames) (b : entryID) (es : List raftpb.Entry)
    (k : Nat) (x : raftpb.Entry) :
    es[k]? = some x → uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    logRecs (GF := GF) γ b es ⊢ ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ x pt := by
  intro Hk Hr
  unfold logRecs
  refine (BigSepL.bigSepL_lookup (Φ := fun k e =>
    if uint.Z b.index' + (k : Int) + 1 < 2 ^ 64
    then iprop(∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ e pt)
    else iprop(True)) Hk).trans ?_
  simp only [Hr, ↓reduceIte]
  exact .rfl
private theorem leadLogOwn_leader (γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) :
    s.role = .leader →
    leadLogOwn (GF := GF) γ s terms =
      iprop(∃ γt, ∃ (M : GMap w64 (raftpb.Entry × w64)), ∃ l0,
        ⌜terms !! s.term = some ((γt, s.base), l0)⌝ ∗
        ghostMapAuth γt 1 M ∗
        ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ∗
        ⌜∀ i, (M !! i).isSome → uint.Z i ≤ plogLastIndexZ s.base s.log⌝ ∗
        ⌜l0 <+: s.log⌝ ∗
        leadFrags γt l0 s.log) := by
  intro H; unfold leadLogOwn; rw [H]

private theorem campOwn_leader (γ : RaftNames) (id : w64) (s : PState) (F : List raftpb.Entry) :
    s.role = .leader →
    campOwn (GF := GF) γ id s F =
      iprop(∃ F0, isCamp γ id s.term F0 ∗
       ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
         (plogLast base0 F).term' = s.term⌝) := by
  intro H; unfold campOwn; rw [H]

private theorem acksOk_leader (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    s.role = .leader → ⊢ acksOk (GF := GF) γ s acks := by
  intro H; unfold acksOk; rw [H]; exact true_intro
private theorem campOwn_cand (γ : RaftNames) (id : w64) (s : PState) (F : List raftpb.Entry) :
    s.role = .candidate → campOwn (GF := GF) γ id s F = isCamp γ id s.term F := by
  intro H; unfold campOwn; rw [H]
-- END HELPERS (Lean addition)

/-- `Step.win`: allocate the term log -- recording the candidate's base and log, and
holding the leader's entry -- and acknowledge the old and the new last index. -/
theorem ownRaftGhost_step_win (γ : RaftNames) (id : w64) (s : PState)
    (mt : GMap w64 w64) (ms : List Msg) :
    s.role = .candidate →
    IsQuorum γ.reCfg (granted s.votes) →
    plogLastIndexZ s.base s.log + 1 < 2 ^ 64 →
    LeaderMatchOk id s mt →
    (∀ m ∈ ms, ReplOk id (pwinState id s mt) m) →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗
      ownRaftGhost γ id (psendMsgs (pwinState id s mt)
                           ([pselfAck id (pwinState id s mt)] ++ ms)) := by
  intro Hrole Hq Hnw Hmt Hms
  obtain ⟨Hmid, Hmoth⟩ := Hmt
  have Hs2log : (pwinState id s mt).log = s.log ++ [pleaderEntry s] := rfl
  have Hs2out : (pwinState id s mt).outbox = s.outbox := rfl
  have Hs2term : (pwinState id s mt).term = s.term := rfl
  have Hs2vote : (pwinState id s mt).vote = s.vote := rfl
  have Hs2votes : (pwinState id s mt).votes = ∅ := rfl
  have Hs2role : (pwinState id s mt).role = .leader := rfl
  have Hs2commit : (pwinState id s mt).commit = s.commit := rfl
  have Hs2base : (pwinState id s mt).base = s.base := rfl
  have Hs2matched : (pwinState id s mt).matched = mt := rfl
  have Hs2rd : (pwinState id s mt).rd = rdNL s.rd := rfl
  generalize pwinState id s mt = s2 at Hs2log Hs2out Hs2term Hs2vote Hs2votes Hs2role Hs2commit Hs2base Hs2matched Hs2rd Hms ⊢
  have Hcnt := rdCount_replOk id s2 ms Hms
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  have Hsbnd := bnd_le s kl
  iunfold ownLogGhost at Hlg
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  -- the winning quorum, frozen
  have Hwfree : wins !! s.term = none := by
    cases Ht : wins !! s.term with
    | none => rfl
    | some _ =>
      exfalso
      rcases Hwins_ok s.term (by rw [Ht]; rfl) with Hlt | ⟨-, Hr⟩
      · omega
      · rw [Hrole] at Hr; cases Hr
  imod ghost_map_insert_persist s.term (granted s.votes) Hwfree $$ Hwins with ⟨Hwins, #Hwf⟩
  ihave #Hwin : isWin γ id s.term (granted s.votes) $$ []
  · unfold isWin
    iexists γw
    isplitr
    · ipureintro; exact ⟨Hwname, Hq⟩
    isplitr
    · iexact Hwf
    · iexact Htally
  ihave #Hnewlead : isLeader γ id s.term $$ []
  · unfold isLeader; iexists _; iexact Hwin
  obtain ⟨Hwf, Hbc, Hcl⟩ := Hlog_ok
  obtain ⟨Hfp, Hwl, Htle⟩ := Hfull
  rw [campOwn_cand γ id s _ Hrole]
  have HwF : PlogWf base0 (fp ++ s.log) := full_wf _ _ _ Hfp Hwl
  have Hfree : terms !! s.term = none := by
    cases Ht : terms !! s.term with
    | none => rfl
    | some _ =>
      exfalso
      rcases Hterms_ok s.term (by rw [Ht]; rfl) with Hlt | ⟨-, Hr⟩
      · omega
      · rw [Hrole] at Hr; cases Hr
  generalize HL : plogLastIndexZ s.base s.log = L at Hnw Hcl
  have HL0 : 0 ≤ L := by rw [← HL]; exact plogLastIndexZ_nonneg _ _
  have HLF : plogLastIndexZ base0 (fp ++ s.log) = L := by rw [← HL]; exact full_last_index _ _ _ Hfp
  have HlastF : plogLast base0 (fp ++ s.log) = plogLast s.base s.log := full_last _ _ _ Hfp
  have Heidx : uint.Z (pleaderEntry s).Index' = L + 1 := by
    have := stamp_index_eq L 0 HL0 (by omega)
    unfold pleaderEntry stamp plastIndex
    rw [HL]; dsimp only
    rw [this]; omega
  have Hpt0 : uint.Z (plogLast s.base s.log).term' < uint.Z s.term := by
    have Hlt := plogTermAt_last base0 (fp ++ s.log) HwF
    rw [HlastF] at Hlt
    exact (Htle _ _ Hlt).2 Hrole
  generalize He : pleaderEntry s = e at Heidx Hs2log
  have Heterm : e.Term' = s.term := by rw [← He]; rfl
  generalize Hpt : (plogLast s.base s.log).term' = pt0 at Hpt0
  imod ghost_map_alloc (GF := GF) ({[e.Index' := (e, pt0)]} : GMap w64 (raftpb.Entry × w64)) with
    ⟨%γt, Htauth, Htel⟩
  ihave Htel := BigSepM.bigSepM_lookup (Φ := fun i (x : raftpb.Entry × w64) => iprop(i ↪[γt] x))
    (GMap.lookup_singleton_eq e.Index' (e, pt0)) $$ Htel
  imod ghostMapElem_persist $$ Htel with #Htel
  imod ghost_map_insert_persist s.term ((γt, s.base), s.log) Hfree $$ Hterms with ⟨Hterms, #Htnew⟩
  ihave #Htl : isTermLog γ id s.term γt s.base s.log $$ []
  · unfold isTermLog; iexists γm; isplitr
    · ipureintro; exact Htname
    · iexact Htnew
  ihave #He : isEntryR γ e pt0 $$ []
  · unfold isEntryR
    iexists id, γt, s.base, s.log, (fp ++ s.log)
    rw [Heterm]
    iframe Hnewlead Htl Hcown Htel
    isplitr
    · ipureintro
      unfold PtOk
      rw [HLF, Heidx, HlastF, Hpt]
      exact ⟨by omega, by omega, fun _ => rfl, fun h => by omega⟩
    -- a new leader's own entry: the zero slice (2026-10-10)
    unfold entData
    iexists none
    unfold entDataIs
    ipureintro
    rw [← He]; rfl
  have Hwl2 : PlogWf s.base s2.log := by
    rw [Hs2log]
    refine (PlogWf_app _ _ _).mpr ⟨Hwl, fun k x Hk => ?_⟩
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hk
      subst Hk
      rw [Heidx, ← HL]; unfold plogLastIndexZ; push_cast; omega
    | succ k => simp at Hk
  have HF2 : fp ++ s2.log = (fp ++ s.log) ++ [e] := by rw [Hs2log, List.append_assoc]
  have HwF2 : PlogWf base0 (fp ++ s2.log) := full_wf s.base fp s2.log Hfp Hwl2
  have HLF2 : plogLastIndexZ base0 (fp ++ s2.log) = L + 1 := by
    rw [HF2]; unfold plogLastIndexZ at HLF ⊢
    rw [List.length_append]; push_cast; simp at HLF ⊢; omega
  have HkeepF : ∀ j : w64, (plogTermAt base0 (fp ++ s.log) j).isSome →
      plogTermAt base0 (fp ++ s2.log) j = plogTermAt base0 (fp ++ s.log) j := by
    intro j Hj
    rw [HF2]
    apply plogTermAt_app_l
    cases Hx : plogTermAt base0 (fp ++ s.log) j with
    | none => rw [Hx] at Hj; cases Hj
    | some x => exact (plogTermAt_some_range _ _ _ _ Hx).2
  have HtF2 : ∀ (j x : w64), plogTermAt base0 (fp ++ s2.log) j = some x →
      uint.Z x ≤ uint.Z s.term := by
    intro j x Hx
    have Hj := (plogTermAt_some_range _ _ _ _ Hx).2
    rw [HLF2] at Hj
    by_cases Hle : uint.Z j ≤ L
    · rw [HF2, plogTermAt_app_l _ _ _ _ (by rw [HLF]; exact Hle)] at Hx
      exact (Htle _ _ Hx).1
    · rw [HF2, plogTermAt_app_r _ _ _ _ (by rw [HLF]; omega)] at Hx
      have : (uint.Z j - plogLastIndexZ base0 (fp ++ s.log) - 1).toNat = 0 := by rw [HLF]; omega
      rw [this] at Hx
      simp only [List.getElem?_cons_zero, Option.map_eq_map, Option.map_some, Option.some.injEq] at Hx
      rw [← Hx, Heterm]; exact Int.le_refl _
  have HbZ := uint_Z_nonneg s.base.index'
  have HlenL : uint.Z s.base.index' + (s.log.length : Int) = L := by rw [← HL]; rfl
  ihave #Hrecs2 : logRecs γ s.base s2.log $$ []
  · rw [Hs2log]
    iapply logRecs_intro
    imodintro
    iintro %k %x Hk
    ipure Hk
    obtain ⟨Hk, Hr⟩ := Hk
    by_cases Hkl : k < s.log.length
    · rw [List.getElem?_append_left Hkl] at Hk
      icases logRecs_elem γ s.base s.log k x Hk Hr $$ Hrecs with ⟨%pt, %Hpt', #Hx⟩
      iexists pt
      iframe Hx
      ipureintro
      rw [plogTermAt_app_l]
      · exact Hpt'
      · unfold pidx plogLastIndexZ; rw [uint_Z_W64 _ (by omega) (by omega)]; omega
    · rw [List.getElem?_append_right (by omega)] at Hk
      have Hk0 : k - s.log.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp Hk).1; simp at this; omega
      rw [Hk0] at Hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hk
      subst Hk
      iexists pt0
      iframe He
      ipureintro
      have Hp : pidx s.base k = W64 L := by unfold pidx; congr 1; omega
      rw [Hp, plogTermAt_app_l _ _ _ _ (by rw [uint_Z_W64 _ HL0 (by omega), HL]; exact Int.le_refl _),
        ← HL, plogTermAt_last_r _ _ Hwf (by omega), Hpt]
  ihave #HrF2 := logRecs_full γ s.base fp s2.log Hfp $$ Hfrecs Hrecs2
  ihave #Hlf2 : leadFrags γt s.log s2.log $$ []
  · rw [Hs2log]
    unfold leadFrags
    iapply (BigSepL.bigSepL_append (Φ := fun k (e : raftpb.Entry) =>
      if s.log.length ≤ k then iprop(∃ pt : w64, e.Index' ↪[γt]□ ((e, pt) : raftpb.Entry × w64))
      else iprop(True))).2
    isplitr
    · iapply BigSepL.bigSepL_forall_elim
      iintro %k %x Hk
      ipure Hk
      have : ¬ s.log.length ≤ k := by have := (List.getElem?_eq_some_iff.mp Hk).1; omega
      simp only [this, ↓reduceIte]
      itrivial
    · iapply (BigSepL.bigSepL_singleton (Φ := fun k (e : raftpb.Entry) =>
        if s.log.length ≤ k + s.log.length
        then iprop(∃ pt : w64, e.Index' ↪[γt]□ ((e, pt) : raftpb.Entry × w64))
        else iprop(True))).2
      simp only [Nat.zero_add, Nat.le_refl, ↓reduceIte]
      iexists pt0
      iexact Htel
  ihave #Hp2 : leadPrefix γ id s2.term s2.base s2.log $$ []
  · unfold leadPrefix
    rw [Hs2term, Hs2base]
    isplitr
    · iexact Hnewlead
    iexists γt, s.log
    iframe Htl Hrecs2 Hlf2
    ipureintro
    exact ⟨PlogWf_wfR _ _ Hwl2, by rw [Hs2log]; exact List.prefix_append _ _⟩
  ihave #Hpf2 : lpfull γ id s2.term s2.base s2.log fp $$ []
  · unfold lpfull
    rw [Hs2term, Hs2base]
    iexists (fp ++ s.log)
    iframe Hcown Hfrecs
    ipureintro
    exact ⟨Hfp, by rw [HF2]; exact List.prefix_append _ _, Hwl2, HtF2⟩
  ihave #Hfull2 := leadFull_intro $$ Hp2 Hpf2
  ihave #Hnewlead2 : isLeader γ id s2.term $$ []
  · rw [Hs2term]; iexact Hnewlead
  ihave #Hcommit2 : commitIn γ (fp ++ s2.log) s2.commit s2.term $$ []
  · rw [Hs2commit, Hs2term]
    iapply commitIn_agree γ (fp ++ s.log) _ s.commit s.term s.term (Int.le_refl _)
      (HkeepF s.commit (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _,
        by rw [HLF]; exact Hcl⟩)) $$ Hcommit
  ihave #Hbase2 : baseOk γ s2.base $$ []
  · rw [Hs2base]; iexact Hbase
  have Hbnd2 : bnd s2 (some id) = uint.Z s.term + 1 := by unfold bnd; rw [Hs2term]
  -- the two acknowledgements, with their histories
  ihave #Hhnew : ∀ i : w64, ⌜uint.Z i ≤ L + 1⌝ -∗ hist γ (fp ++ s2.log) s2.term i (bnd s2 (some id)) $$ []
  · iintro %i %Hi
    rw [Hbnd2]
    iapply hist_of_agree γ (fp ++ s2.log) (fp ++ s2.log) s2.term i _ HwF2
      (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HLF2]; exact Hi⟩)
      rfl $$ HrF2
    unfold okL
    ileft
    iexists s2.term
    isplitr
    · ipureintro; rw [Hs2term]; omega
    · iexact Hfull2
  ihave #Hhists2 : histsOk γ s2 (some id) (fp ++ s2.log) acks $$ []
  · unfold histsOk
    rw [Hbnd2]
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %k %u %Hk #Hk
    iapply hist_mono γ (fp ++ s2.log) k.1 k.2 (bnd s kl) (uint.Z s.term + 1) Hsbnd
    iapply hist_keep γ (fp ++ s.log) _ k.1 k.2 (bnd s kl) (fun j _ hj => HkeepF j hj) $$ Hk
  ihave #Hvlogs2 : vlogsOk γ s2 acks vlogs $$ []
  · rw [show vlogsOk (GF := GF) γ s2 acks vlogs = vlogsOk γ s acks vlogs by unfold vlogsOk; rw [Hs2term]]
    iexact Hvlogs_ok
  have HplZ : uint.Z (plastIndex s) = L := by
    unfold plastIndex; rw [HL, uint_Z_W64 _ HL0 (by omega)]
  have HLs2 : plogLastIndexZ s2.base s2.log = L + 1 := by
    rw [Hs2base, Hs2log]; unfold plogLastIndexZ at HL ⊢
    rw [List.length_append]; simp at HL ⊢; omega
  have HplZ2 : uint.Z (plastIndex s2) = L + 1 := by
    unfold plastIndex; rw [HLs2, uint_Z_W64 _ (by omega) (by omega)]
  ihave ⟨#Hhists3, #Hvlogs3⟩ := ack_invs_insert γ s2 (some id) (fp ++ s2.log) acks vlogs (plastIndex s)
    $$ [] Hhists2 Hvlogs2
  · iapply Hhnew; ipureintro; omega
  ihave ⟨#Hhists4, #Hvlogs4⟩ := ack_invs_insert γ s2 (some id) (fp ++ s2.log) _ vlogs (plastIndex s2)
    $$ [] Hhists3 Hvlogs3
  · iapply Hhnew; ipureintro; omega
  imod acks_add γa acks (s2.term, plastIndex s) $$ Hacks Hafrags with ⟨Hacks, #Hafr1, #Hk1⟩
  imod acks_add γa _ (s2.term, plastIndex s2) $$ Hacks Hafr1 with ⟨Hacks, #Hafr2, #Hk2⟩
  ihave Hevs : ownEvs γ id s2.term acks $$ [Hevs]
  · rw [Hs2term]; iexact Hevs
  imod ownEvs_ack γ id s2.term acks (plastIndex s) $$ Hevs with ⟨Hevs, #Hev1⟩
  imod ownEvs_ack γ id s2.term _ (plastIndex s2) $$ Hevs with ⟨Hevs, #Hev2⟩
  ihave #Hcmt2 : isCommitted γ (cprefix fp s2) $$ []
  · rw [show cprefix fp s2 = (fp ++ s.log ++ [e]).take (uint.Z s.commit).toNat by
        unfold cprefix; rw [Hs2log, Hs2commit, List.append_assoc]]
    rw [cprefix_app fp s [e] (by
      have := Hfp.1
      rw [List.length_append]; push_cast; omega)]
    iexact Hcmt
  -- the log ghost state of the new leader
  have Hterms_ok' : TermsOk (<[s.term := ((γt, s.base), s.log)]> terms) s2 := by
    intro t Ht
    rw [Hs2term, Hs2role]
    by_cases Htt : t = s.term
    · right; exact ⟨Htt, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Htt)] at Ht
      rcases Hterms_ok t Ht with Hlt | ⟨-, Hr⟩
      · left; exact Hlt
      · rw [Hrole] at Hr; cases Hr
  have Hwins_ok' : WinsOk (<[s.term := granted s.votes]> wins) s2 := by
    intro t Ht
    rw [Hs2term, Hs2role]
    by_cases Htt : t = s.term
    · right; exact ⟨Htt, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Htt)] at Ht
      rcases Hwins_ok t Ht with Hlt | ⟨-, Hr⟩
      · left; exact Hlt
      · rw [Hrole] at Hr; cases Hr
  have Hacks_term' : AcksTerm s2 (<[(s2.term, plastIndex s2) := ()]>
      (<[(s2.term, plastIndex s) := ()]> acks)) := by
    apply AcksTerm_insert _ _ _ _ (Int.le_refl _)
    apply AcksTerm_insert _ _ _ _ (Int.le_refl _)
    intro k Hk; rw [Hs2term]; exact Hacks_term k Hk
  have Hlog_ok' : LogOk s2 := by
    refine ⟨PlogWf_wfR _ _ (by rw [Hs2base]; exact Hwl2), by rw [Hs2base, Hs2commit]; exact Hbc, ?_⟩
    rw [HLs2, Hs2commit]; omega
  have Hfull' : FullOk s2.base fp ∧ PlogWf s2.base s2.log ∧ TermsLe s2 (fp ++ s2.log) := by
    refine ⟨by rw [Hs2base]; exact Hfp, by rw [Hs2base]; exact Hwl2, fun j x Hx => ?_⟩
    rw [Hs2term, Hs2role]
    exact ⟨HtF2 j x Hx, fun h => by cases h⟩
  have Hcamps_ok' : ∀ T, (camps !! T).isSome → uint.Z T ≤ uint.Z s2.term := by
    intro T HT; rw [Hs2term]; exact Hcamps_ok T HT
  ihave #Hcown2 : campOwn γ id s2 (fp ++ s2.log) $$ []
  · rw [campOwn_leader γ id s2 _ Hs2role, Hs2term]
    iexists (fp ++ s.log)
    iframe Hcown
    ipureintro
    refine ⟨by rw [HF2]; exact List.prefix_append _ _, by rw [HLF, HLF2]; omega, ?_⟩
    rw [HF2]
    unfold plogLast
    rw [List.getLast?_append]
    simp only [List.getLast?_singleton, Option.some_or]
    exact Heterm
  ihave Htlog' : leadLogOwn γ s2 (<[s.term := ((γt, s.base), s.log)]> terms) $$ [Htauth]
  · rw [leadLogOwn_leader γ s2 _ Hs2role, Hs2term, Hs2base]
    iexists γt, ({[e.Index' := (e, pt0)]} : GMap w64 (raftpb.Entry × w64)), s.log
    iframe Htauth Hlf2
    isplitr
    · ipureintro; exact GMap.lookup_insert_eq _ _ _
    isplitr
    · unfold GMap.singleton
      iapply (BigSepM.bigSepM_insert (Φ := fun i (x : raftpb.Entry × w64) => iprop(i ↪[γt]□ x))
        (GMap.lookup_empty _)).2
      isplitr
      · iexact Htel
      · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro
    refine ⟨fun i Hi => ?_, by rw [Hs2log]; exact List.prefix_append _ _⟩
    by_cases Hie : i = e.Index'
    · rw [Hie, Heidx, ← Hs2base, HLs2]; exact Int.le_refl _
    · rw [GMap.lookup_singleton_ne _ (Ne.symm Hie)] at Hi; cases Hi
  ihave #Hmatched' : matchedOk γ s2 $$ []
  · rw [matchedOk_leader γ s2 Hs2role, Hs2matched, Hs2term]
    iapply BigSepM.bigSepM_forall_elim
    iintro %v %x %Hv
    by_cases Hvid : v = id
    · have Hv' : mt !! id = some x := by rw [← Hvid]; exact Hv
      rw [Hmid] at Hv'; cases Hv'
      rw [Hvid]
      unfold isAcked
      iright
      isplitr
      · iexists γa; isplitr
        · ipureintro; exact Haname
        · rw [← Hs2term]; iexact Hk1
      · rw [← Hs2term]; iexact Hev1
    · rw [Hmoth v x Hvid Hv]
      unfold isAcked; ileft; ipureintro; rfl
  ihave #Hacks_ok' : acksOk γ s2 (<[(s2.term, plastIndex s2) := ()]>
      (<[(s2.term, plastIndex s) := ()]> acks)) $$ []
  · iapply acksOk_leader γ s2 _ Hs2role
  ihave #Hcommit' := Hcommit2
  ihave #Htfrags' : ([∗map] t ↦ x ∈ <[s.term := ((γt, s.base), s.log)]> terms, t ↪[γm]□ x) $$ []
  · iapply (BigSepM.bigSepM_insert (Φ := fun t (x : TermRec) => iprop(t ↪[γm]□ x)) Hfree).2
    isplitr
    · iexact Htnew
    · iexact Htfrags
  ihave #Hkl' : klOk γ id s2 (some id) $$ []
  · unfold klOk
    isplitr
    · iexists (granted s.votes)
      rw [Hs2term]
      iframe Hwin
      ipureintro
      intro Hv; exfalso; apply Hidnz
      rw [← Hv, Hs2vote]; exact (Hrole_ok.1 (by rw [Hrole]; intro h; cases h)).symm
    · ipureintro; intro _; rfl
  ihave #Hrecs2' : logRecs γ s2.base s2.log $$ []
  · rw [Hs2base]; iexact Hrecs2
  ihave Hlg : ownLogGhost γ id s2 (some id) $$ [Hterms Hacks Hcamps Hvlogs Htlog' Hwins Hevs]
  · unfold ownLogGhost
    iexists γm, (<[s.term := ((γt, s.base), s.log)]> terms), γa, _, fp, γc, camps, γl, vlogs, γw,
      (<[s.term := granted s.votes]> wins)
    iframe % # ∗
  have Hwl2' : PlogWfR s2.base s2.log := by rw [Hs2base]; exact PlogWf_wfR _ _ Hwl2
  -- the commit lower bound of the new term (2026-10-12)
  imod lcmOwn_win γ id s s2 (by rw [Hrole]; decide) Hs2role Hs2term
    (by rw [Hs2commit]; exact Int.le_refl _) $$ Hlcm with Hlcm
  -- the read registry of the new term (2026-10-13)
  imod rdOwn_win γ id s (psendMsgs s2 ([pselfAck id s2] ++ ms)) (by rw [Hrole]; decide) Hs2role
    Hs2term Hs2rd
    (by
      show rdCount (s2.outbox ++ ([pselfAck id s2] ++ ms)) ≤ rdCount s.outbox
      rw [rdCount_append, rdCount_append, rdCount_singleton, Hs2out, Hcnt]
      simp [pselfAck]) $$ Hrd with Hrd
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted (some id) Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro
    exact VoteHistOk_eq voted s _ Hhist (by show s2.term = s.term; exact Hs2term)
      (by show s2.vote = s.vote; exact Hs2vote)
  · rw [psendMsgs_outbox, Hs2out]
    iapply outbox_app $$ Hout
    iapply outbox_app
    · iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
      unfold pselfAck
      iapply isMessage_appResp
      unfold isAcked
      iright
      isplitr
      · iexists γa
        isplitr
        · ipureintro; exact Haname
        · iexact Hk2
      · iexact Hev2
    · iapply BigSepL.bigSepL_forall_elim
      iintro %k %x %Hk
      iapply replOk_message γ id s2 x fp Hwl2' (Hms x (List.mem_of_getElem? Hk)) Hidnz $$
        Hnewlead2 Hp2 Hpf2 Hrecs2' Hcommit2 Hbase2 Hcmt2
  · iapply tally_empty γ id _ (by show s2.votes = ∅; exact Hs2votes)
  · unfold leaderWit
    simp only [psendMsgs_role, Hs2role, psendMsgs_term]
    iexact Hnewlead2
  · iapply ownLogGhost_mono γ id s2 _ (some id) (by rfl) (by rfl) (by rfl)
      (by intro h; exact ⟨h, rfl, rfl⟩) (by intro h; exact ⟨h, rfl⟩) (by exact fun h => h) (by rfl)
      (by exact fun h => h) $$ Hlg
  · ipureintro
    intro Hr; exfalso; apply Hr; show s2.role = .leader; exact Hs2role
  · ipureintro
    intro h
    have h' : s2.role = .follower := h
    rw [Hs2role] at h'; cases h'
  · ipureintro
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · show s2.vote = id
      rw [Hs2vote]; exact Hrole_ok.1 (by rw [Hrole]; intro h; cases h)
    · have h' : s2.role = .candidate := h
      rw [Hs2role] at h'; cases h'
  · lcm_mono
  · iexact Hrd

/-- `Step.beat`: a heartbeat carries the leadership, a commit index the leader has, and
the `Match` it is bounded by. -/
theorem ownRaftGhost_step_beat (γ : RaftNames) (id : w64) (s : PState) (ms : List Msg) :
    s.role = .leader →
    (∀ m ∈ ms, HeartbeatOk id s m) →
    (∀ m ∈ ms, m.ctx = hbCtx s.rd.ro) →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗ ownRaftGhost γ id (psendMsgs s ms) := by
  intro Hrole Hms Hctx
  have Hcnt : rdCount ms = 0 := by
    unfold rdCount; rw [List.countP_eq_zero]
    intro m hm; simp [(Hms m hm).1]
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave #Hhb := rdOwn_hbCtx γ id s Hrole $$ Hrd
  ihave #Hmatched := ownLogGhost_matched $$ Hlg
  ihave #Hl : isLeader γ id s.term $$ []
  · unfold leaderWit; rw [Hrole]; iexact Hlead
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  icases ownLogGhost_lead_full γ id s kl Hrole $$ Hl Hlg with ⟨⟨%fp, #Hp, #Hpf, #Hc⟩, Hlg⟩
  ihave #Hfl := leadFull_intro $$ Hp Hpf
  ihave ⟨%HwF, #HrF⟩ := leadFull_wf $$ Hfl
  ihave ⟨%fp1, %Hfp1, #Hfr1, #Hcm1⟩ := ownLogGhost_cmt $$ Hlg
  ihave ⟨#Hfrp, %Hfp⟩ := lpfull_fp $$ Hpf
  ihave #Hcmt := cprefix_transfer γ fp1 fp s Hfp1 Hfp.1 $$ Hfr1 Hfrp Hcm1
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]
    iapply outbox_app $$ Hout
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %m %Hk
    obtain ⟨Hty, Hfrom, Hterm, -, Hcm, Hmatch⟩ := Hms m (List.mem_of_getElem? Hk)
    simp only [isMessage, Hty, Hfrom, Hterm]
    isplitr
    · iexact Hl
    isplitr
    · iexists (fp ++ s.log)
      isplitr
      · iexact Hfl
      isplitr
      · iapply commitIn_le γ _ s.commit m.commit s.term HwF.1 Hcm $$ HrF Hc
      · iapply isCommitted_mono γ ((fp ++ s.log).take (uint.Z m.commit).toNat) (cprefix fp s)
          (take_prefix_le _ _ _ (by omega)) $$ Hcmt
    isplitr
    · unfold matchOf at Hmatch
      cases Hx : s.matched !! m.dst with
      | some x =>
        rw [Hx] at Hmatch
        iexists x
        isplitr
        · ipureintro; exact Hmatch
        · unfold matchedOk; rw [Hrole]
          iapply BigSepM.bigSepM_lookup Hx $$ Hmatched
      | none =>
        iexists (W64 0)
        isplitr
        · ipureintro; rw [Hx] at Hmatch; exact Hmatch
        · unfold isAcked; ileft; ipureintro; rfl
    isplitr
    · ipureintro; exact Hidnz
    · rw [Hctx m (List.mem_of_getElem? Hk)]
      iexact Hhb
  · iapply tally_eq γ id s (psendMsgs s _) rfl rfl $$ Htally
  · iapply leaderWit_eq γ id s (psendMsgs s _) rfl rfl $$ Hlead
  · iapply ownLogGhost_mono γ id s (psendMsgs s _) kl rfl rfl rfl (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · lcm_mono
  · rd_mono

/-- `Step.sendApps`: as `Step.win`'s broadcast. -/
theorem ownRaftGhost_step_send_apps (γ : RaftNames) (id : w64) (s : PState)
    (ms : List Msg) :
    s.role = .leader →
    (∀ m ∈ ms, ReplOk id s m) →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗ ownRaftGhost γ id (psendMsgs s ms) := by
  intro Hrole Hms
  have Hcnt := rdCount_replOk id s ms Hms
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  ihave #Hb := ownLogGhost_base $$ Hlg
  ihave #Hl : isLeader γ id s.term $$ []
  · unfold leaderWit; rw [Hrole]; iexact Hlead
  icases ownLogGhost_lead_full γ id s kl Hrole $$ Hl Hlg with ⟨⟨%fp, #Hp, #Hpf, #Hc⟩, Hlg⟩
  ihave ⟨%fp1, %Hfp1, #Hfr1, #Hcm1⟩ := ownLogGhost_cmt $$ Hlg
  ihave ⟨#Hfrp, %Hfp⟩ := lpfull_fp $$ Hpf
  ihave #Hcmt := cprefix_transfer γ fp1 fp s Hfp1 Hfp.1 $$ Hfr1 Hfrp Hcm1
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]
    iapply outbox_app $$ Hout
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %m %Hk
    iapply replOk_message γ id s m fp Hok.1 (Hms m (List.mem_of_getElem? Hk)) Hidnz $$
      Hl Hp Hpf Hrecs Hc Hb Hcmt
  · iapply tally_eq γ id s (psendMsgs s _) rfl rfl $$ Htally
  · iapply leaderWit_eq γ id s (psendMsgs s _) rfl rfl $$ Hlead
  · iapply ownLogGhost_mono γ id s (psendMsgs s _) kl rfl rfl rfl (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · lcm_mono
  · rd_mono

/-- `Step.propForward`: the forwarded proposal carries the received one's entries, and
what it says of them (2026-10-10). -/
theorem ownRaftGhost_step_prop_forward (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .propose) :
    ⊢ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs s
           [Msg.mkV .propose id s.lead (W64 0) m.reject
              m.index m.logterm m.commit m.rejecthint
              m.entries [] m.ctx]) := by
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]
    iapply outbox_snoc $$ Hout
    iunfold isMessage at Hm
    rw [Hty]
    icases Hm with ⟨%Hp, #Hed⟩
    unfold isMessage
    isplitr
    · ipureintro; exact ⟨rfl, Hp.2⟩
    · iexact Hed
  · iapply tally_eq γ id s (psendMsgs s _) rfl rfl $$ Htally
  · iapply leaderWit_eq γ id s (psendMsgs s _) rfl rfl $$ Hlead
  · iapply ownLogGhost_mono γ id s (psendMsgs s _) kl rfl rfl rfl (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · lcm_mono
  · rd_mono

/-- `Step.appResp`: the new `Match` is the old one or the acknowledgement the message
carries. -/
theorem ownRaftGhost_step_app_resp (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (x : w64) :
    m.ty = .appResp →
    m.term = s.term →
    s.role = .leader →
    m.reject = false →
    s.matched !! m.src = some x →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        { s with matched :=
            <[m.src := if uint.Z x < uint.Z m.index
                       then m.index else x]> s.matched } := by
  intro Hty Hterm Hrole Hrej Hx
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave #Hack : isAcked γ m.src s.term m.index $$ []
  · rw [← Hterm]; iapply isMessage_appResp_inv γ m Hty Hrej $$ Hm
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · iexact Hout
  · iexact Htally
  · iapply leaderWit_eq γ id s _ (by rfl) (by rfl) $$ Hlead
  · ihave #Hmatched := ownLogGhost_matched $$ Hlg
    iapply ownLogGhost_mono' γ id s _ kl kl (by rfl) (by rfl) (by intro h; exact ⟨h, rfl⟩)
      (by intro h _; exact absurd Hrole h) (by intro h; exact ⟨h, rfl⟩) (by exact Int.le_refl _)
      (by exact Int.le_refl _) (by exact Or.inl ⟨rfl, rfl, fun h => h, fun h => h⟩) (by exact Or.inl rfl)
      $$ Hlg [] [] []
    · rw [matchedOk_leader γ _ Hrole]
      unfold matchedOk; simp only [Hrole]
      iapply BigSepM.bigSepM_insert_elim $$ [] Hmatched
      split
      · iexact Hack
      · iapply BigSepM.bigSepM_lookup Hx $$ Hmatched
    · iintro %fp %_ - #Hc; iexact Hc
    · iintro %fp %_ - #Hc; simp only [cprefix]; iexact Hc
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · lcm_mono
  · rd_mono

/-- `Step.commit`: a quorum of `Match`es at least `n` is a commit fact `cq`, which extends
the global committed log (`commit_extend`, inside the invariant) -- the node's committed
prefix is then `isCommitted`. -/
theorem ownRaftGhost_step_commit (γ : RaftNames) (id : w64) (s : PState) (n : w64) :
    s.role = .leader →
    uint.Z s.commit < uint.Z n →
    uint.Z n ≤ plogLastIndexZ s.base s.log →
    plogTermAt s.base s.log n = some s.term →
    IsQuorum γ.reCfg (ackedBy s n) →
    ⊢ ownRaftGhost (GF := GF) γ id s ={⊤}=∗ ownRaftGhost γ id { s with commit := n } := by
  intro Hrole Hlt Hle Htm Hq
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave #Hl : isLeader γ id s.term $$ []
  · unfold leaderWit; rw [Hrole]; iexact Hlead
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  icases ownLogGhost_lead_full γ id s kl Hrole $$ Hl Hlg with ⟨⟨%fp0, #Hp, #Hpf, -⟩, Hlg⟩
  ihave #Hfl := leadFull_intro $$ Hp Hpf
  ihave ⟨#Hfr0, %Hfull0⟩ := lpfull_fp $$ Hpf
  ihave #Hmatched := ownLogGhost_matched $$ Hlg
  ihave #Hinv := ownLogGhost_inv $$ Hlg
  ihave #Hcq : cq γ s.term n (fp0 ++ s.log) $$ []
  · unfold cq
    isplitr
    · ipureintro
      rw [full_term_at s.base fp0 s.log n Hfull0.1 (by have := Hok.2.1; omega)]
      exact Htm
    isplitr
    · iexact Hfl
    iexists ackedBy s n
    isplitr
    · ipureintro; exact Hq
    rw [matchedOk_leader γ s Hrole]
    iapply BigSepM.bigSepM_forall_elim
    iintro %v %u %Hv
    have Hv' : v ∈ ackedBy s n := (GMap.elem_of_gset _ _).mpr (by cases u; exact Hv)
    unfold ackedBy at Hv'
    obtain ⟨x, Hx⟩ := (GMap.elem_of_dom _ _).mp Hv'
    obtain ⟨Hx, Hle'⟩ := (GMap.mapLookup_filter_Some _ _ _ _).mp Hx
    iexists x
    isplitr
    · ipureintro; simpa using Hle'
    · iapply BigSepM.bigSepM_lookup Hx $$ Hmatched
  imod lcmOwn_commit γ id s { s with commit := n } n Hrole Hrole rfl rfl (Int.le_of_lt Hlt)
    $$ Hlcm with ⟨Hlcm, #Hclb⟩
  imod commit_extend γ s.term n (fp0 ++ s.log) id $$ Hinv Hcq Hl Hclb with #Hcmn
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · iexact Hout
  · iexact Htally
  · iapply leaderWit_eq γ id s _ (by rfl) (by rfl) $$ Hlead
  · iapply ownLogGhost_mono' γ id s _ kl kl (by rfl) (by rfl) (by intro h; exact ⟨h, rfl⟩)
      (by intro h _; exact absurd Hrole h) (by intro h; exact ⟨h, rfl⟩) (by exact Int.le_refl _)
      (by show uint.Z s.commit ≤ uint.Z n; omega)
      (by exact Or.inl ⟨rfl, rfl, fun h => h, fun h => h⟩) (by exact Or.inr Hle)
      $$ Hlg [] [] []
    · iapply matchedOk_eq γ s _ (by rfl) (by rfl) (by rfl) $$ Hmatched
    · iintro %fp % ⟨Hf, -⟩ #Hfr -
      icases FullOk_unique γ s.base fp fp0 Hf Hfull0.1 $$ Hfr Hfr0 with %Heq
      subst Heq
      unfold commitIn
      iright
      iexists s.term, n, (fp ++ s.log)
      iframe Hcq
      ipureintro
      exact ⟨Int.le_refl _, Int.le_refl _, rfl⟩
    · iintro %fp % ⟨Hf, -⟩ #Hfr -
      icases FullOk_unique γ s.base fp fp0 Hf Hfull0.1 $$ Hfr Hfr0 with %Heq
      subst Heq
      simp only [cprefix]; iexact Hcmn
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · iexact Hlcm
  · rd_mono

/-- `Step.appStale`: back to follower of `m.src` in the same term, and acknowledge the
commit index -- which needs no justification. -/
theorem ownRaftGhost_step_app_stale (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .app →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) := by
  intro Hty Hfid Hterm Hrole
  exact ownRaftGhost_step_stale γ id s m (Or.inl Hty) Hfid Hterm Hrole

/-- `Step.appReject`: back to follower of `m.src`; a rejection carries nothing. -/
theorem ownRaftGhost_step_app_reject (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (hint hintterm : w64) :
    m.ty = .app →
    m.src ≠ id →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term true m.index
              hintterm (W64 0) hint []]) := by
  intro _ Hfid Hrole
  iintro #_ Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]; simp only [padoptLeader]
    iapply outbox_snoc $$ Hout
    iapply isMessage_appResp_rej
  · iapply tally_empty γ id _ (by rfl)
  · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
  · iapply ownLogGhost_mono γ id s _ kl (by rfl) (by rfl) (by rfl)
      (by intro h; cases h) (by intro h; cases h) (by intro h; exact absurd h Hrole) (by rfl)
      (by exact fun h => h) $$ Hlg
  · ipureintro; intro _; exact Hfid
  · ipureintro; intro _; rfl
  · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
  · lcm_mono
  · rd_mono

/-! ### Read-index: a node of term `T` dooms no record of `T` (2026-10-13) -/

theorem ownLogGhost_ack_le (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64) (t i : w64) :
    ⊢ ownLogGhost (GF := GF) γ v s kl -∗ ackEv γ v t i -∗ ⌜uint.Z t ≤ uint.Z s.term⌝ := by
  unfold ownLogGhost ownEvs ackEv
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩ ⟨%γe', %L, %HL, #Hlb⟩
  iNamed H
  icases Hevs with ⟨%γe, %evs, %Hγe, Ha, %Hevs⟩
  obtain ⟨Hγe', Hin, -⟩ := HL
  rw [Hγe] at Hγe'; cases Hγe'
  icases mono_list_auth_lb_valid $$ Ha Hlb with %Hp
  ipureintro
  have := Hevs.2.1 _ (Hp.2.subset Hin)
  simpa [aevTerm] using this

theorem ownLogGhost_not_doomed (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (r : RqRec) :
    ⊢ ownLogGhost (GF := GF) γ v s kl -∗ rqRecOk γ s.term r -∗
      ⌜∀ t' q, r.2 = some (t', q) → v ∉ q⌝ := by
  iintro Hown #Hr
  rcases h : r.2 with _ | ⟨t', q⟩ <;> simp only [rqRecOk, h]
  · ipureintro; intro t' q h'; cases h'
  · unfold doomed
    icases Hr with ⟨%Hpq, #Hacks⟩
    have Hlt := Hpq.1
    by_cases hv : v ∈ q
    · ihave ⟨%i', %Hi', #Ha⟩ := BigSepM.bigSepM_lookup
        (Φ := fun v _ => iprop(∃ i', ⌜0 < uint.Z i'⌝ ∗ isAcked (GF := GF) γ v t' i'))
        ((GMap.elem_of_gset _ _).mp hv) $$ Hacks
      unfold isAcked
      icases Ha with (%H0 | ⟨-, #Hev⟩)
      · exfalso; omega
      · ihave %Hle := ownLogGhost_ack_le γ v s kl t' i' $$ Hown Hev
        exfalso; omega
    · ipureintro
      intro t'' q' hh
      cases hh
      exact hv

theorem ownLogGhost_not_doomed_list (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (recs : List RqRec) :
    ⊢ ownLogGhost (GF := GF) γ v s kl -∗ ([∗list] r ∈ recs, rqRecOk γ s.term r) -∗
      ⌜∀ r ∈ recs, ∀ t' q, r.2 = some (t', q) → v ∉ q⌝ := by
  induction recs with
  | nil => iintro _ _; ipureintro; intro r hr; cases hr
  | cons r rs ih =>
    iintro Hown Hl
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨#Hr, #Hrs⟩
    ihave %H1 := ownLogGhost_not_doomed γ v s kl r $$ Hown Hr
    ihave %H2 := ih $$ Hown Hrs
    ipureintro
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | h
    · exact H1
    · exact H2 r' h

/-- A heartbeat's position, acknowledged by a node of the heartbeat's term. -/
theorem ownLogGhost_hbAck (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (q : Nat) (recs : List RqRec) (hq : q ≤ recs.length) :
    ⊢ ownLogGhost (GF := GF) γ v s kl -∗ ([∗list] r ∈ recs, rqRecOk γ s.term r) -∗
      ⌜HbAckOk v q recs⌝ := by
  iintro Hown Hl
  ihave %H := ownLogGhost_not_doomed_list γ v s kl recs $$ Hown Hl
  ipureintro
  exact ⟨hq, fun r hr => H r (List.mem_of_mem_take hr)⟩

/-- A heartbeat's read-index part, at a node of its term, gives its response's. -/
theorem ownLogGhost_hbResp (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (L : w64) (ctx : List w8) :
    ⊢ ownLogGhost (GF := GF) γ v s kl -∗
      (⌜ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜ctx = u64Le q ∧ uint.nat q ≤ recs.length⌝ ∗ rqLb γ L s.term recs ∗
         [∗list] r ∈ recs, rqRecOk γ s.term r) -∗
      (⌜ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜ctx = u64Le q ∧ HbAckOk v (uint.nat q) recs⌝ ∗ rqLb γ L s.term recs) := by
  iintro Hown (%H0 | ⟨%q, %recs, %Hq, #Hlb, #Hrs⟩)
  · ileft; ipureintro; exact H0
  · ihave %Hack := ownLogGhost_hbAck γ v s kl (uint.nat q) recs Hq.2 $$ Hown Hrs
    iright
    iexists q, recs
    iframe Hlb
    ipureintro; exact ⟨Hq.1, Hack⟩

/-- `Step.heartbeat`: back to follower of `m.src`; the new commit index is the old one or
the heartbeat's, which carries `isCommittedIdx` and which the rule's premise puts within
the log. -/
theorem ownRaftGhost_step_heartbeat (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .heartbeat →
    m.dst = id →
    m.term = s.term →
    m.src ≠ id →
    s.role ≠ .leader →
    uint.Z m.commit ≤ plogLastIndexZ s.base s.log →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
           [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }]) := by
  intro Hty Hto Hterm Hfid Hrole Hcm
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases isMessage_heartbeat_inv γ m Hty $$ Hm with
    ⟨-, ⟨%Fl, #Hfl, #Hmc, #Hmcm⟩, ⟨%i, %Hi, #Hack⟩, %Hfnz, #Hctx⟩
  rw [Hto, Hterm] at *
  ihave #Hagree := ownLogGhost_ack_agree γ id s kl i $$ Hlg Hack
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  ihave #Hctx' := ownLogGhost_hbResp γ id s kl m.src m.ctx $$ Hlg Hctx
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]; simp only [padoptLeader]
    iapply outbox_snoc $$ Hout
    unfold isMessage
    simp only [Msg.plain]
    iexact Hctx'
  · iapply tally_empty γ id _ (by rfl)
  · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
  · iapply ownLogGhost_mono' γ id s _ kl kl (by rfl) (by rfl) (by intro h; cases h)
      (by intro _ h; exact absurd h Hrole) (by intro h; cases h) (by exact Int.le_refl _)
      (by exact plogCommitTo_ge _ _)
      (by exact Or.inl ⟨rfl, rfl, fun h => h, fun h => by cases h⟩)
      (by
        show plogCommitTo s.commit m.commit = s.commit ∨
          uint.Z (plogCommitTo s.commit m.commit) ≤ plogLastIndexZ s.base s.log
        unfold plogCommitTo; split
        · exact Or.inr Hcm
        · exact Or.inl rfl)
      $$ Hlg [] [] []
    · iapply matchedOk_nonleader γ _ (by intro h; cases h)
    · iintro %fp % ⟨Hf, Hw⟩ #Hfr #Hc
      simp only [psendMsgs, padoptLeader, plogCommitTo]
      split
      · rename_i Hlt
        have Hci : uint.Z s.commit < uint.Z i := by omega
        ihave #Ha := Hagree $$ %(⟨Hrole, Hci⟩)
        icases ackAgree_full γ s.base s.log fp s.term i Hf (by have := Hok.2.1; omega) $$ Ha with
          ⟨%X, #HX, %HsX, %HXi⟩
        ihave #HrF := logRecs_full γ s.base fp s.log Hf $$ Hfr Hrecs
        have HwF := full_wf _ _ _ Hf Hw
        icases leadFull_wf γ s.term X $$ HX with ⟨%HwX, #HrX⟩
        ihave %Hmt := full_match γ X (fp ++ s.log) i HwX.1 HwF HsX HXi $$ HrX HrF
        iunfold commitIn at Hmc
        icases Hmc with (%H0 | ⟨%t, %n, %G, #Hq, %Hc', %Ht, %HG⟩)
        · exfalso; have := uint_Z_nonneg s.commit; omega
        ihave ⟨%HwG, -⟩ := cq_full $$ Hq
        ihave %Hn := cq_term $$ Hq
        have HsG : (plogTermAt base0 G m.commit).isSome :=
          full_term_at_some G m.commit n (by rw [Hn]; rfl) Hc'
        ihave %HXl := leadFull_agree γ s.term X Fl m.commit
          (full_term_at_some X m.commit i HsX (by omega)) (by rw [← HG]; exact HsG) $$ HX Hfl
        unfold commitIn
        iright
        iexists t, n, G
        isplitr
        · iexact Hq
        · ipureintro
          exact ⟨Hc', Ht, HG.trans (HXl.symm.trans (Hmt m.commit (by omega)))⟩
      · iexact Hc
    · iintro %fp % ⟨Hf, Hw⟩ #Hfr #Hcm0
      simp only [cprefix, psendMsgs, padoptLeader, plogCommitTo]
      split
      · rename_i Hlt
        have Hci : uint.Z s.commit < uint.Z i := by omega
        ihave #Ha := Hagree $$ %(⟨Hrole, Hci⟩)
        icases ackAgree_full γ s.base s.log fp s.term i Hf (by have := Hok.2.1; omega) $$ Ha with
          ⟨%X, #HX, %HsX, %HXi⟩
        ihave #HrF := logRecs_full γ s.base fp s.log Hf $$ Hfr Hrecs
        have HwF := full_wf _ _ _ Hf Hw
        icases leadFull_wf γ s.term X $$ HX with ⟨%HwX, #HrX⟩
        icases leadFull_wf γ s.term Fl $$ Hfl with ⟨%HwFl, #HrFl⟩
        ihave %Hmt := full_match γ X (fp ++ s.log) i HwX.1 HwF HsX HXi $$ HrX HrF
        iunfold commitIn at Hmc
        icases Hmc with (%H0 | ⟨%t, %n, %G, #Hq, %Hc', %Ht, %HG⟩)
        · exfalso; have := uint_Z_nonneg s.commit; omega
        ihave %Hn := cq_term $$ Hq
        have HsG : (plogTermAt base0 G m.commit).isSome :=
          full_term_at_some G m.commit n (by rw [Hn]; rfl) Hc'
        have HsXc : (plogTermAt base0 X m.commit).isSome :=
          full_term_at_some X m.commit i HsX (by omega)
        ihave %HXl := leadFull_agree γ s.term X Fl m.commit HsXc (by rw [← HG]; exact HsG) $$ HX Hfl
        have HmX := Hmt m.commit (by omega)
        ihave %Htk := full_take_eq γ (fp ++ s.log) Fl m.commit HwF HwFl.1 (by rw [← HmX]; exact HsXc)
          (by rw [← HmX]; exact HXl) $$ HrF HrFl
        rw [Htk]; iexact Hmcm
      · iexact Hcm0
  · ipureintro; intro _; exact Hfid
  · ipureintro; intro _; rfl
  · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
  · lcm_mono
  · rd_mono

/-- `Step.appAccept`. The new log is the old one cut at the first conflict, if any, and
the batch appended (`plogMaybeAppend_inv`); the batch is the leader's (`isMessage`'s
`leadPrefix`). So the new log has records (the old ones below the cut; the leader's
above, whose predecessor terms are the batch's, which the new log has:
`plogMaybeAppend_batch`, `plog_prefix_batch`); every justified acknowledgement of this
term is below the cut (`ackAgree_term`: the old log agrees with the leader there, and
the cut is where it does not); and the new acknowledgement of `lastnewi` is justified by
the batch itself. -/
theorem ownRaftGhost_step_app_accept (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (lastnewi : w64) (es' : List raftpb.Entry) :
    m.ty = .app →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit ≤ uint.Z m.index →
    plogMaybeAppend s.base s.log
      (entryID.mk m.logterm m.index) m.entries
      = some (lastnewi, es') →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with
               log := es',
               commit := plogCommitTo s.commit
                           (if uint.Z m.commit < uint.Z lastnewi
                            then m.commit else lastnewi) }
           [Msg.mk .appResp id m.src s.term false lastnewi
              (W64 0) (W64 0) (W64 0) []]) := by
  intro Hty Hfid Hterm Hrole Hcidx Happ
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases isMessage_app_inv γ m Hty $$ Hm with
    ⟨%Hpay, #Hl, ⟨%bL, %l', %fpL, #Hp', %Hpl, #Hpf', #Hmc, #Hmcm⟩, %Hfnz⟩
  obtain ⟨Hprev', Hpre'⟩ := Hpl
  rw [Hterm]
  ihave #HLf := leadFull_intro $$ Hp' Hpf'
  icases leadFull_wf γ s.term (fpL ++ l') $$ HLf with ⟨%HwLf, #HrLf⟩
  icases lpfull_fp $$ Hpf' with ⟨-, %HfL⟩
  obtain ⟨Hwfb, Hnw, -⟩ := Hpay
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  ihave %Hwl := ownLogGhost_wf $$ Hlg
  obtain ⟨Hwf, Hbc, Hcl⟩ := Hok
  obtain ⟨Hmatch, Hli, Hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ Hwfb Hnw Happ
  have Hmatch' : plogTermAt s.base s.log m.index = some m.logterm := Hmatch
  obtain ⟨Hwf', Hlast'⟩ := plogMaybeAppend_wfR _ _ _ _ _ _ Hwf Hwfb Hnw Happ
  have Hbatch := plogMaybeAppend_batch _ _ _ _ _ _ Hwfb Hnw Happ
  have Hlb := plog_prefix_batch bL l' (entryID.mk m.logterm m.index) m.entries Hnw Hprev' Hpre'
  simp only at Hli Hbatch Hlb Hnw
  have Hpb := (plogTermAt_some_range _ _ _ _ Hmatch').1
  have Hpl := (plogTermAt_some_range _ _ _ _ Hmatch').2
  have HbL := (plogTermAt_some_range _ _ _ _ Hprev').1
  have Hagree : ∀ j : w64, uint.Z m.index ≤ uint.Z j →
      uint.Z j ≤ uint.Z m.index + (m.entries.length : Int) →
      plogTermAt s.base es' j = plogTermAt bL l' j ∧ (plogTermAt bL l' j).isSome := by
    intro j Hj1 Hj2
    rw [Hbatch j Hj1 Hj2, Hlb j Hj1 Hj2]
    refine ⟨rfl, plogTermAt_in_range _ _ _ ⟨Hj1, ?_⟩⟩
    unfold plogLastIndexZ; exact Hj2
  have Hc'1 : uint.Z s.commit ≤ uint.Z (plogCommitTo s.commit
      (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi)) := plogCommitTo_ge _ _
  have Hc'2 : uint.Z (plogCommitTo s.commit
      (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi)) ≤ uint.Z lastnewi ∨
      plogCommitTo s.commit
      (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) = s.commit := by
    unfold plogCommitTo
    by_cases h : uint.Z s.commit <
        uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi)
    · simp only [h, ↓reduceIte]; left; split <;> omega
    · simp only [h, ↓reduceIte]; right; trivial
  have HbZ := uint_Z_nonneg s.base.index'
  have HmZ := uint_Z_lt m.index
  -- the new log's records
  ihave #Hrecs' : logRecs γ s.base es' $$ []
  · rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
    · iexact Hrecs
    dsimp only at Hei
    icases leadPrefix_wf γ m.src s.term bL l' $$ Hp' with ⟨%Hwfl, #Hrl⟩
    have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
    subst Hes'
    iapply logRecs_intro
    imodintro
    iintro %k %x Hk
    ipure Hk
    obtain ⟨Hk, Hr⟩ := Hk
    · have Hn : (uint.Z e.Index' - uint.Z s.base.index' - 1).toNat ≤ s.log.length := by
        unfold plogLastIndexZ at Hend; omega
      by_cases Hkn : k < (uint.Z e.Index' - uint.Z s.base.index' - 1).toNat
      · rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take] at Hk
        simp only [Hkn, ↓reduceIte] at Hk
        icases logRecs_elem γ s.base s.log k x Hk (by omega) $$ Hrecs with ⟨%pt, %Hpt, #Hx⟩
        iexists pt
        iframe Hx
        ipureintro
        rw [← Hpt]
        apply plog_cut_keep _ _ _ _ _ ⟨by omega, by omega⟩
        unfold pidx
        rw [uint_Z_W64 _ (by omega) (by omega)]
        omega
      · have Hk' := Hk
        rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
          Nat.min_eq_left Hn, List.getElem?_drop] at Hk'
        have Hkk := (List.getElem?_eq_some_iff.mp Hk').1
        have Hx' := prefix_lookup_Some Hk' Hpre'
        unfold plogFrom at Hx'
        rw [List.getElem?_drop] at Hx'
        have Hadd : uint.Z (m.index + W64 1) = uint.Z m.index + 1 := by word
        rw [Hadd] at Hx'
        icases logRecs_elem γ bL l' _ x Hx' (by omega) $$ Hrl with ⟨%pt, %Hpt, #Hx⟩
        iexists pt
        iframe Hx
        ipureintro
        have Hpj : pidx s.base k = W64 (uint.Z m.index +
            ((d + (k - (uint.Z e.Index' - uint.Z s.base.index' - 1).toNat) : Nat) : Int)) := by
          unfold pidx; congr 1; omega
        have Hpj' : pidx bL ((uint.Z m.index + 1 - uint.Z bL.index' - 1).toNat +
            (d + (k - (uint.Z e.Index' - uint.Z s.base.index' - 1).toNat))) =
            W64 (uint.Z m.index +
              ((d + (k - (uint.Z e.Index' - uint.Z s.base.index' - 1).toNat) : Nat) : Int)) := by
          unfold pidx; congr 1; omega
        rw [Hpj'] at Hpt
        rw [Hpj, ← Hpt]
        refine (Hagree _ ?_ ?_).1
        · rw [uint_Z_W64 _ (by omega) (by omega)]; omega
        · rw [uint_Z_W64 _ (by omega) (by omega)]; omega
  -- every justified acknowledgement of this term is below the cut
  ihave #Hkeep : □ (⌜s.term = s.term⌝ -∗ ∀ i,
      ⌜uint.Z (plogCommitTo s.commit
        (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi)) < uint.Z i⌝ -∗
      ackAgree γ s.base s.log s.term i -∗ ackAgree γ s.base es' s.term i) $$ []
  · imodintro
    iintro - %i %Hi #Ha
    rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
    · iexact Ha
    dsimp only at Hei
    have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
    by_cases Hlt : uint.Z i < uint.Z e.Index'
    · iunfold ackAgree at Ha
      icases Ha with ⟨%Hil, %ldr, %bL0, %l0, #Hp0, %Hs0, %fp0, #Hpf0⟩
      unfold ackAgree
      isplitr
      · ipureintro
        rw [Hes', plog_cut_last _ _ _ _ ⟨by omega, Hend⟩, List.length_drop]
        omega
      iexists ldr, bL0, l0
      isplitr
      · iexact Hp0
      isplitr
      · ipureintro
        refine ⟨Hs0.1, Hs0.2.trans ?_⟩
        rw [Hes', plog_cut_keep _ _ _ _ _ ⟨by omega, Hend⟩ Hlt]
      · iexists fp0; iexact Hpf0
    · have Hj := Hagree e.Index' (by omega) (by omega)
      ihave %Hj' := ackAgree_term γ s.base s.log s.term i m.src bL l' e.Index' Hwf (by omega)
        (by omega) (by omega) Hj.2 $$ Hrecs Ha Hp'
      exfalso
      apply Hnm
      show plogTermAt s.base s.log e.Index' = some e.Term'
      rw [Hj', Hlb e.Index' (by omega) (by omega)]
      exact plogTermAt_lookup _ _ _ d e Hd (by simp only; omega)
  -- the new log's last index
  have Hlast'' : plogLastIndexZ s.base es' < 2 ^ 64 ∧
      (es' ≠ s.log → plogLastIndexZ s.base es' = uint.Z lastnewi) := by
    rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
    · exact ⟨PlogWf_range _ _ Hwl, fun h => absurd rfl h⟩
    · dsimp only at Hei
      have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
      rw [Hes', plog_cut_last _ _ _ _ ⟨by omega, Hend⟩, List.length_drop]
      constructor
      · omega
      · intro _; omega
  have Hwl' : PlogWf s.base es' := PlogWfR_wf _ _ Hwf' Hlast''.1
  -- the new log, as a full log
  have Hfull_new : ∀ fp, FullOk s.base fp →
      (∀ j : w64, uint.Z j ≤ uint.Z m.index →
         plogTermAt base0 (fp ++ es') j = plogTermAt base0 (fp ++ s.log) j) ∧
      (∀ j : w64, uint.Z m.index ≤ uint.Z j → uint.Z j ≤ uint.Z lastnewi →
         plogTermAt base0 (fp ++ es') j = plogTermAt base0 (fpL ++ l') j ∧
         (plogTermAt base0 (fpL ++ l') j).isSome) := by
    intro fp Hf
    constructor
    · intro j Hj
      by_cases Hjb : uint.Z j < uint.Z s.base.index'
      · rw [full_term_at_le s.base fp es' j Hf (by omega),
          full_term_at_le s.base fp s.log j Hf (by omega)]
      · rw [full_term_at s.base fp es' j Hf (by omega), full_term_at s.base fp s.log j Hf (by omega)]
        by_cases Hjm : uint.Z j = uint.Z m.index
        · have : j = m.index := uint_Z_inj.mp Hjm
          rw [this, (Hagree m.index (Int.le_refl _) (by omega)).1, Hprev', Hmatch']
        · rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
          · rfl
          · dsimp only at Hei
            rw [Hes', plog_cut_keep _ _ _ _ _ ⟨by omega, Hend⟩ (by omega)]
    · intro j Hj1 Hj2
      obtain ⟨Heq, Hs⟩ := Hagree j Hj1 (by omega)
      rw [full_term_at s.base fp es' j Hf (by omega), full_term_at bL fpL l' j HfL.1 (by omega)]
      exact ⟨Heq, Hs⟩
  ihave #Hb := ownLogGhost_base $$ Hlg
  -- learn the leader
  iunfold isLeader at Hl
  icases Hl with ⟨%qw, #Hwin⟩
  ihave %Hex := vote_excl γ id s γv voted m.src qw Hname Hhist $$ Hvoted Hwin
  ihave Hlg := ownLogGhost_learn γ id s kl m.src qw Hrole $$ Hwin %Hex Hlg
  have HlastZ : uint.Z lastnewi < 2 ^ 64 := uint_Z_lt lastnewi
  ihave Hlg := ownLogGhost_upd γ id s
      { padoptLeader s m.src with
          log := es',
          commit := plogCommitTo s.commit
            (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
      (some m.src) (some m.src)
      (by intro h; cases h) (by intro _ h; exact absurd h Hrole) (by intro h; cases h)
      (Int.le_refl _) Hc'1
      (Or.inl ⟨rfl, rfl, fun h => h, fun h => by cases h⟩)
      (by
        refine ⟨Hwf', ?_, ?_⟩ <;> dsimp only [padoptLeader]
        · omega
        · rcases Hc'2 with h | h
          · omega
          · rw [h]; omega)
      $$ Hlg [] [] [] [] []
  · imodintro
    iintro - %i %Hi #Ha
    simp only [padoptLeader] at Hi ⊢
    iapply Hkeep $$ [] %i [] Ha
    · ipureintro; trivial
    · ipureintro; exact Hi
  · simp only [padoptLeader]; iexact Hrecs'
  · iapply matchedOk_nonleader γ _ (by intro h; cases h)
  · simp only [padoptLeader]; iexact Hb
  · iintro %fp %Hf3 #Hfr #Hc #Hcm0
    obtain ⟨Hf, Hw, Htle⟩ := Hf3
    obtain ⟨Hlow, Hmid⟩ := Hfull_new fp Hf
    ihave #HrF' := logRecs_full γ s.base fp es' Hf $$ Hfr Hrecs'
    ihave #HrF := logRecs_full γ s.base fp s.log Hf $$ Hfr Hrecs
    have HwF' := full_wf _ _ _ Hf Hwl'
    have HwF := full_wf _ _ _ Hf Hw
    obtain ⟨Hli', Hsli⟩ := Hmid lastnewi (by omega) (Int.le_refl _)
    ihave %HmL := full_match γ (fpL ++ l') (fp ++ es') lastnewi HwLf.1 HwF' Hsli Hli'.symm $$ HrLf HrF'
    have HlastF' : plogLastIndexZ base0 (fp ++ es') = plogLastIndexZ s.base es' :=
      full_last_index _ _ _ Hf
    iexists fp
    isplitr
    · ipureintro
      refine ⟨⟨Hf, Hwl', ?_⟩, fun Hr => absurd rfl Hr⟩
      intro j x Hx
      refine ⟨?_, fun h => by cases h⟩
      show uint.Z x ≤ uint.Z s.term
      by_cases Hjm : uint.Z j ≤ uint.Z m.index
      · rw [Hlow j Hjm] at Hx; exact (Htle j x Hx).1
      by_cases HjL : uint.Z j ≤ uint.Z lastnewi
      · rw [(Hmid j (by omega) HjL).1] at Hx; exact HwLf.2 j x Hx
      rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
      · exact (Htle j x Hx).1
      · exfalso
        have Hr := (plogTermAt_some_range _ _ _ _ Hx).2
        rw [HlastF'] at Hr
        have Hne : es' ≠ s.log := by
          intro Heq
          dsimp only at Hei
          have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
          apply Hnm
          show plogTermAt s.base s.log e.Index' = some e.Term'
          rw [← Heq, Hbatch e.Index' (by omega) (by omega)]
          exact plogTermAt_lookup _ _ _ d e Hd (by simp only; omega)
        rw [Hlast''.2 Hne] at Hr
        omega
    isplitr
    · iexact Hfr
    have HXle : uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) ≤ uint.Z lastnewi := by split <;> omega
    have HXm : uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) ≤ uint.Z m.commit := by split <;> omega
    isplitr
    · simp only [padoptLeader, plogCommitTo]
      generalize (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) = X at HXle HXm ⊢
      split
      · iapply commitIn_agree γ (fpL ++ l') (fp ++ es') X s.term s.term (Int.le_refl _)
          (HmL X HXle).symm
        iapply commitIn_le γ (fpL ++ l') m.commit X s.term HwLf.1 HXm $$ HrLf Hmc
      · iapply commitIn_agree γ (fp ++ s.log) (fp ++ es') s.commit s.term s.term (Int.le_refl _)
          (Hlow s.commit Hcidx) $$ Hc
    isplitr
    · simp only [cprefix, plogCommitTo]
      generalize (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) = X at HXle HXm ⊢
      split
      · ihave %Htk := full_take_eq γ (fpL ++ l') (fp ++ es') X HwLf.1 HwF'
          (full_term_at_some _ _ lastnewi Hsli HXle) (HmL X HXle) $$ HrLf HrF'
        rw [← Htk]
        iapply isCommitted_mono γ _ _ (take_prefix_le _ _ _ (by omega)) $$ Hmcm
      · ihave %Htk := full_take_eq γ (fp ++ s.log) (fp ++ es') s.commit HwF HwF'
          (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _,
            by rw [full_last_index _ _ _ Hf]; exact Hcl⟩)
          (Hlow s.commit Hcidx).symm $$ HrF HrF'
        rw [← Htk]; iexact Hcm0
    · imodintro
      iintro %t %i %Ht #Hh
      simp only [bnd, padoptLeader]
      rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
      · iexact Hh
      dsimp only at Hei
      have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
      iapply hist_replace γ (fp ++ s.log) (fp ++ es') (fpL ++ l') t i s.term
        (uint.Z s.term + 1) (uint.Z s.term + 1) (uint.Z e.Index') e.Index' lastnewi
        (Int.le_refl _) Ht (by omega) (by omega) ⟨Int.le_refl _, by omega⟩
        ?_ ?_ ?_ ?_ $$ HLf Hh
      · intro j Hj
        by_cases Hjb : uint.Z j < uint.Z s.base.index'
        · rw [full_term_at_le s.base fp es' j Hf (by omega),
            full_term_at_le s.base fp s.log j Hf (by omega)]
        · rw [full_term_at s.base fp es' j Hf (by omega),
            full_term_at s.base fp s.log j Hf (by omega), Hes',
            plog_cut_keep _ _ _ _ _ ⟨by omega, Hend⟩ Hj]
      · intro j Hj
        exact Hmid j (by omega) Hj.2
      · rw [full_term_at s.base fp s.log e.Index' Hf (by omega),
          full_term_at bL fpL l' e.Index' HfL.1 (by omega), Hlb e.Index' (by omega) (by omega),
          plogTermAt_lookup _ _ _ d e Hd (by simp only; omega)]
        exact Hnm
      · intro j Hj
        refine (plogTermAt_none_range _ _ _).mpr (Or.inr ?_)
        rw [HlastF', Hes', plog_cut_last _ _ _ _ ⟨by omega, Hend⟩, List.length_drop]
        omega
  imod ownLogGhost_ack γ id
      { padoptLeader s m.src with
          log := es',
          commit := plogCommitTo s.commit
            (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
      (some m.src) lastnewi $$ [] [] Hlg with ⟨Hlg, #Hack⟩
  · unfold ackOk
    iintro %_
    simp only [padoptLeader]
    unfold ackAgree
    isplitr
    · ipureintro; exact Hlast'
    iexists m.src, bL, l'
    isplitr
    · iexact Hp'
    isplitr
    · ipureintro
      obtain ⟨Heq, Hs⟩ := Hagree lastnewi (by omega) (by omega)
      exact ⟨Hs, Heq.symm⟩
    · iexists fpL; iexact Hpf'
  · iintro %fp %Hf2 #Hfr -
    obtain ⟨Hf, Hw⟩ := Hf2
    simp only [padoptLeader, bnd] at Hf Hw ⊢
    obtain ⟨-, Hmid⟩ := Hfull_new fp Hf
    ihave #HrF' := logRecs_full γ s.base fp es' Hf $$ Hfr Hrecs'
    obtain ⟨Hli', Hsli⟩ := Hmid lastnewi (by omega) (Int.le_refl _)
    iapply hist_of_agree γ (fp ++ es') (fpL ++ l') s.term lastnewi _ (full_wf _ _ _ Hf Hw) Hsli
      Hli'.symm $$ HrF'
    unfold okL
    ileft
    iexists s.term
    isplitr
    · ipureintro; omega
    · iexact HLf
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted (some m.src) Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]; simp only [padoptLeader]
    iapply outbox_snoc $$ Hout
    iapply isMessage_appResp $$ Hack
  · iapply tally_empty γ id _ (by rfl)
  · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
  · iapply ownLogGhost_mono γ id
      { padoptLeader s m.src with
          log := es',
          commit := plogCommitTo s.commit
            (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) } _ (some m.src)
      (by rfl) (by rfl) (by rfl)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by rfl) (by exact fun h => h)
      $$ Hlg
  · ipureintro; intro _; exact Hfid
  · ipureintro; intro _; rfl
  · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
  · lcm_mono
  · rd_mono

/-- Freezing a batch of stamped entries into the leader's term log: their indices are
past everything in it (`leadLogOwn`'s bound) and do not wrap. Each is frozen with the
predecessor term `ptf k`. -/
theorem term_log_insert_stamped (γt : GName) (M : GMap w64 (raftpb.Entry × w64)) (T : w64)
    (L : Int) (ents : List raftpb.Entry) (ptf : Nat → w64) :
    0 ≤ L → L + (ents.length : Int) < 2 ^ 64 →
    (∀ i, (M !! i).isSome → uint.Z i ≤ L) →
    ⊢ ghostMapAuth (GF := GF) γt 1 M -∗ ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ==∗
      ∃ M' : GMap w64 (raftpb.Entry × w64),
        ghostMapAuth γt 1 M' ∗ ([∗map] i ↦ e ∈ M', i ↪[γt]□ e) ∗
        ⌜∀ i, (M' !! i).isSome → uint.Z i ≤ L + (ents.length : Int)⌝ ∗
        [∗list] k ↦ e ∈ ents.mapIdx (stamp T (W64 L)),
          e.Index' ↪[γt]□ ((e, ptf k) : raftpb.Entry × w64) := by
  intro HL Hnw Hdom
  obtain ⟨r, rfl⟩ : ∃ r, ents = r.reverse := ⟨ents.reverse, by simp⟩
  induction r with
  | nil =>
    iintro Hauth #Hfr
    imodintro
    iexists M
    iframe Hauth Hfr
    isplitr
    · ipureintro; intro i Hi; have := Hdom i Hi; simp only [List.reverse_nil, List.length_nil]; omega
    · rw [List.reverse_nil, List.mapIdx_nil]; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x r IH =>
    rw [List.reverse_cons] at Hnw ⊢
    generalize r.reverse = ents at Hnw IH ⊢
    simp only [List.length_append, List.length_singleton] at Hnw
    iintro Hauth #Hfr
    imod IH (by omega) $$ Hauth Hfr with ⟨%M', Hauth, #Hfr', %Hdom', #Hents⟩
    have Hidx : uint.Z (stamp T (W64 L) ents.length x).Index' = L + 1 + ents.length := by
      simp only [stamp]; exact stamp_index_eq L ents.length HL (by omega)
    have Hfresh : M' !! (stamp T (W64 L) ents.length x).Index' = none := by
      cases Hm : M' !! (stamp T (W64 L) ents.length x).Index' with
      | none => rfl
      | some _ =>
        have := Hdom' _ (by rw [Hm]; rfl)
        omega
    imod ghost_map_insert_persist _ ((stamp T (W64 L) ents.length x), ptf ents.length) Hfresh $$ Hauth
      with ⟨Hauth, #Hnew⟩
    imodintro
    iexists M'.insert (stamp T (W64 L) ents.length x).Index' ((stamp T (W64 L) ents.length x), ptf ents.length)
    iframe Hauth
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun i e => iprop(i ↪[γt]□ e)) Hfresh).2
      isplitr
      · iexact Hnew
      · iexact Hfr'
    isplitr
    · ipureintro
      intro i Hi
      simp only [List.length_append, List.length_singleton]
      by_cases Hie : i = (stamp T (W64 L) ents.length x).Index'
      · rw [Hie, Hidx]; omega
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hie)] at Hi
        have := Hdom' i Hi; omega
    · rw [List.mapIdx_concat]
      iapply (BigSepL.bigSepL_snoc (Φ := fun k (e : raftpb.Entry) =>
        iprop(e.Index' ↪[γt]□ ((e, ptf k) : raftpb.Entry × w64)))).2
      isplitr
      · iexact Hents
      · rw [List.length_mapIdx]; iexact Hnew

/-- Stamping keeps the entries' data (2026-10-10). -/
private theorem entData_mapIdx_stamp (γ : RaftNames) (t L : w64) (ents : List raftpb.Entry) :
    ⊢ ([∗list] e ∈ ents, entData (GF := GF) γ e) -∗
      [∗list] x ∈ ents.mapIdx (stamp t L), entData γ x := by
  iintro #H
  iapply BigSepL.bigSepL_intro (P := iprop(□ [∗list] e ∈ ents, entData (GF := GF) γ e))
  · intro k x Hk
    rw [List.getElem?_mapIdx] at Hk
    cases Hy : ents[k]? with
    | none => rw [Hy] at Hk; cases Hk
    | some y =>
      rw [Hy] at Hk; cases Hk
      iintro #Hl
      rw [show stamp t L k y = { y with Term' := t, Index' := L + W64 1 + W64 k } from rfl,
        entData_stamp]
      iapply BigSepL.bigSepL_lookup (Φ := fun _ (e : raftpb.Entry) => entData (GF := GF) γ e)
        Hy $$ Hl
  · iexact H

/-- `Step.propose`: the stamped entries go into the leader's term log
(`term_log_insert_stamped`), which gives each its `isEntryR` (the first after the old
last entry, the rest after each other); the self-acknowledgement is the node's own to
allocate. (Rocq's `let s' := pappend s (imap …) in` is inlined.) -/
theorem ownRaftGhost_step_propose (γ : RaftNames) (id : w64) (s : PState)
    (ents : List raftpb.Entry) :
    s.role = .leader →
    plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
    ⊢ ([∗list] e ∈ ents, entData (GF := GF) γ e) -∗ ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))
          [pselfAck id (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))]) := by
  intro Hrole Hnw
  rw [show plastIndex s = W64 (plogLastIndexZ s.base s.log) from rfl]
  generalize HL : plogLastIndexZ s.base s.log = L at Hnw ⊢
  iintro #Hed Hown
  ihave #Hnwd := entData_mapIdx_stamp γ s.term (W64 L) ents $$ Hed
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave #Hl : isLeader γ id s.term $$ []
  · unfold leaderWit; rw [Hrole]; iexact Hlead
  iunfold ownLogGhost at Hlg
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  rw [leadLogOwn_leader γ s terms Hrole]
  icases Htlog with ⟨%γt, %M, %l0, %Hγt, Htauth, #Htel, %Hdom, %Hpre, #Hlf⟩
  rw [campOwn_leader γ id s _ Hrole]
  icases Hcown with ⟨%F0, #Hc0, %HF0⟩
  obtain ⟨Hwf, Hbc, Hcl⟩ := Hlog_ok
  obtain ⟨Hfp, Hwl, Htle⟩ := Hfull
  have HL0 : 0 ≤ L := by rw [← HL]; exact plogLastIndexZ_nonneg _ _
  have HLF : plogLastIndexZ base0 (fp ++ s.log) = L := by rw [← HL]; exact full_last_index _ _ _ Hfp
  have Hpt0 : (plogLast s.base s.log).term' = s.term := by
    rw [← full_last s.base fp s.log Hfp]; exact HF0.2.2
  imod term_log_insert_stamped γt M s.term L ents (fun _ => s.term) HL0 Hnw (by rw [← HL]; exact Hdom) $$ Htauth Htel with
    ⟨%M', Htauth, #Htel', %Hdom', #Hnew⟩
  ihave #Htl : isTermLog γ id s.term γt s.base l0 $$ []
  · unfold isTermLog
    iexists γm
    isplitr
    · ipureintro; exact Htname
    · iapply BigSepM.bigSepM_lookup (Φ := fun t (x : TermRec) => iprop(t ↪[γm]□ x)) Hγt $$ Htfrags
  have Hnwk : ∀ (k : Nat) (x : raftpb.Entry), (ents.mapIdx (stamp s.term (W64 L)))[k]? = some x →
      uint.Z x.Index' = L + 1 + k ∧ x.Term' = s.term := by
    intro k x Hk
    rw [List.getElem?_mapIdx] at Hk
    cases Hy : ents[k]? with
    | none => rw [Hy] at Hk; cases Hk
    | some y =>
      rw [Hy] at Hk; cases Hk
      have := (List.getElem?_eq_some_iff.mp Hy).1
      exact ⟨stamp_index_eq L k HL0 (by omega), rfl⟩
  have Hlen : (ents.mapIdx (stamp s.term (W64 L))).length = ents.length := List.length_mapIdx
  generalize Hnwdef : ents.mapIdx (stamp s.term (W64 L)) = nw at Hnwk Hlen ⊢
  have HlenL : uint.Z s.base.index' + (s.log.length : Int) = L := by rw [← HL]; rfl
  have HbZ := uint_Z_nonneg s.base.index'
  ihave #Hrecs' : logRecs γ s.base (s.log ++ nw) $$ []
  · iapply logRecs_intro
    imodintro
    iintro %k %x Hk
    ipure Hk
    obtain ⟨Hk, Hr⟩ := Hk
    by_cases Hkl : k < s.log.length
    · rw [List.getElem?_append_left Hkl] at Hk
      icases logRecs_elem γ s.base s.log k x Hk Hr $$ Hrecs with ⟨%pt, %Hpt, #Hx⟩
      iexists pt
      iframe Hx
      ipureintro
      rw [plogTermAt_app_l]
      · exact Hpt
      · unfold pidx plogLastIndexZ; rw [uint_Z_W64 _ (by omega) (by omega)]; omega
    · rw [List.getElem?_append_right (by omega)] at Hk
      obtain ⟨Hxi, Hxt⟩ := Hnwk _ x Hk
      ihave #Hxe := BigSepL.bigSepL_lookup (Φ := fun k (e : raftpb.Entry) =>
        iprop(e.Index' ↪[γt]□ ((e, s.term) : raftpb.Entry × w64))) Hk $$ Hnew
      iexists s.term
      isplitr
      · ipureintro
        have Hp : pidx s.base k = W64 (L + ((k - s.log.length : Nat) : Int)) := by
          unfold pidx; congr 1; omega
        rw [Hp]
        by_cases Hk0 : k - s.log.length = 0
        · rw [Hk0, plogTermAt_app_l]
          · rw [show L + ((0 : Nat) : Int) = L by omega, ← HL, plogTermAt_last_r _ _ Hwf (by omega), Hpt0]
          · rw [uint_Z_W64 _ (by omega) (by omega), HL]; omega
        · rw [plogTermAt_app_r _ _ _ _ (by rw [uint_Z_W64 _ (by omega) (by omega), HL]; omega)]
          have Hy : (k - s.log.length - 1) < nw.length := by
            have := (List.getElem?_eq_some_iff.mp Hk).1; omega
          obtain ⟨y, Hy'⟩ : ∃ y, nw[k - s.log.length - 1]? = some y :=
            ⟨_, List.getElem?_eq_getElem Hy⟩
          have : (uint.Z (W64 (L + ((k - s.log.length : Nat) : Int))) -
              plogLastIndexZ s.base s.log - 1).toNat = k - s.log.length - 1 := by
            rw [uint_Z_W64 _ (by omega) (by omega), HL]; omega
          rw [this, Hy']
          simp only [Option.map_eq_map, Option.map_some]
          rw [(Hnwk _ y Hy').2]
      · unfold isEntryR
        iexists id, γt, s.base, l0, F0
        rw [Hxt]
        iframe Hl Htl Hc0 Hxe
        isplitr
        · ipureintro
          rw [HLF] at HF0
          unfold PtOk
          refine ⟨by omega, Int.le_refl _, fun h => by omega, fun _ => rfl⟩
        iapply BigSepL.bigSepL_lookup (Φ := fun _ (e : raftpb.Entry) => entData (GF := GF) γ e)
          Hk $$ Hnwd
  ihave #Hlf' : leadFrags γt l0 (s.log ++ nw) $$ []
  · unfold leadFrags
    iapply (BigSepL.bigSepL_append (Φ := fun k (e : raftpb.Entry) =>
      if l0.length ≤ k then iprop(∃ pt : w64, e.Index' ↪[γt]□ ((e, pt) : raftpb.Entry × w64))
      else iprop(True))).2
    isplitr
    · iexact Hlf
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %x Hk
    ipure Hk
    have Hle : l0.length ≤ k + s.log.length := by have := Hpre.length_le; omega
    simp only [Hle, ↓reduceIte]
    iexists s.term
    iapply BigSepL.bigSepL_lookup (Φ := fun k (e : raftpb.Entry) =>
        iprop(e.Index' ↪[γt]□ ((e, s.term) : raftpb.Entry × w64))) Hk $$ Hnew
  have Hwl' : PlogWf s.base (s.log ++ nw) :=
    (PlogWf_app _ _ _).mpr ⟨Hwl, fun k e Hk => by have := (Hnwk k e Hk).1; push_cast; omega⟩
  have HkeepF : ∀ j : w64, (plogTermAt base0 (fp ++ s.log) j).isSome →
      plogTermAt base0 (fp ++ (s.log ++ nw)) j = plogTermAt base0 (fp ++ s.log) j := by
    intro j Hj
    rw [← List.append_assoc]
    apply plogTermAt_app_l
    cases Hx : plogTermAt base0 (fp ++ s.log) j with
    | none => rw [Hx] at Hj; cases Hj
    | some x => exact (plogTermAt_some_range _ _ _ _ Hx).2
  have HtF' : TermsLe (pappend s nw) (fp ++ (pappend s nw).log) := by
    intro j x Hx
    refine ⟨?_, fun h => by rw [show (pappend s nw).role = s.role from rfl, Hrole] at h; cases h⟩
    show uint.Z x ≤ uint.Z s.term
    have Hx' : plogTermAt base0 ((fp ++ s.log) ++ nw) j = some x := by
      rw [List.append_assoc]; exact Hx
    by_cases Hj : uint.Z j ≤ L
    · rw [plogTermAt_app_l _ _ _ _ (by rw [HLF]; exact Hj)] at Hx'
      exact (Htle j x Hx').1
    · rw [plogTermAt_app_r _ _ _ _ (by rw [HLF]; omega)] at Hx'
      cases Hy : nw[(uint.Z j - plogLastIndexZ base0 (fp ++ s.log) - 1).toNat]? with
      | none => rw [Hy] at Hx'; cases Hx'
      | some y =>
        rw [Hy] at Hx'
        simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at Hx'
        rw [← Hx', (Hnwk _ y Hy).2]; exact Int.le_refl _
  have Hlog_ok' : LogOk (pappend s nw) := by
    refine ⟨PlogWf_wfR _ _ Hwl', Hbc, ?_⟩
    show uint.Z s.commit ≤ plogLastIndexZ s.base (s.log ++ nw)
    unfold plogLastIndexZ at Hcl ⊢
    rw [List.length_append]; push_cast; omega
  have Hfull' : FullOk (pappend s nw).base fp ∧ PlogWf (pappend s nw).base (pappend s nw).log ∧
      TermsLe (pappend s nw) (fp ++ (pappend s nw).log) := ⟨Hfp, Hwl', HtF'⟩
  ihave #Hcown' : campOwn γ id (pappend s nw) (fp ++ (pappend s nw).log) $$ []
  · rw [campOwn_leader γ id (pappend s nw) _ Hrole, show (pappend s nw).term = s.term from rfl]
    iexists F0
    iframe Hc0
    ipureintro
    refine ⟨HF0.1.trans (by rw [show (pappend s nw).log = s.log ++ nw from rfl,
      ← List.append_assoc]; exact List.prefix_append _ _), ?_, ?_⟩
    · have := HF0.2.1
      show _ < plogLastIndexZ base0 (fp ++ (s.log ++ nw))
      have Heq : plogLastIndexZ base0 (fp ++ (s.log ++ nw)) =
          plogLastIndexZ base0 (fp ++ s.log) + (nw.length : Int) := by
        unfold plogLastIndexZ; simp only [List.length_append]; push_cast; omega
      omega
    · show (plogLast base0 (fp ++ (s.log ++ nw))).term' = s.term
      unfold plogLast
      rw [← List.append_assoc, List.getLast?_append]
      cases Hy : nw.getLast? with
      | none =>
        simp only [Option.none_or]
        have := HF0.2.2
        unfold plogLast at this
        exact this
      | some y =>
        simp only [Option.some_or]
        exact (Hnwk _ y (getLast?_some_getElem? _ _ Hy)).2
  ihave #Hhists' : histsOk γ (pappend s nw) kl (fp ++ (pappend s nw).log) acks $$ []
  · unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %k %u %Hk #Hk
    rw [show (pappend s nw).log = s.log ++ nw from rfl, show bnd (pappend s nw) kl = bnd s kl from rfl]
    iapply hist_keep γ (fp ++ s.log) _ k.1 k.2 (bnd s kl) (fun j _ hj => HkeepF j hj) $$ Hk
  ihave #Hcommit' : commitIn γ (fp ++ (pappend s nw).log) (pappend s nw).commit (pappend s nw).term $$ []
  · rw [show (pappend s nw).log = s.log ++ nw from rfl, show (pappend s nw).commit = s.commit from rfl,
      show (pappend s nw).term = s.term from rfl]
    iapply commitIn_agree γ (fp ++ s.log) _ s.commit s.term s.term (Int.le_refl _)
      (HkeepF s.commit (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _,
        by rw [HLF, ← HL]; exact Hcl⟩)) $$ Hcommit
  ihave Htlog' : leadLogOwn γ (pappend s nw) terms $$ [Htauth]
  · rw [leadLogOwn_leader γ (pappend s nw) terms Hrole, show (pappend s nw).term = s.term from rfl,
      show (pappend s nw).base = s.base from rfl, show (pappend s nw).log = s.log ++ nw from rfl]
    iexists γt, M', l0
    iframe Htauth Htel' Hlf'
    ipureintro
    refine ⟨Hγt, fun i Hi => ?_, Hpre.trans (List.prefix_append _ _)⟩
    have := Hdom' i Hi
    show uint.Z i ≤ plogLastIndexZ s.base (s.log ++ nw)
    unfold plogLastIndexZ at HL ⊢
    rw [List.length_append]; push_cast; omega
  ihave #Hmatched' : matchedOk γ (pappend s nw) $$ []
  · iapply matchedOk_eq γ s _ (by rfl) (by rfl) (by rfl) $$ Hmatched
  ihave #Hacks_ok' : acksOk γ (pappend s nw) acks $$ []
  · iapply acksOk_leader γ (pappend s nw) acks Hrole
  ihave #Hkl' := klOk_step γ id s (pappend s nw) kl kl (Or.inl ⟨rfl, rfl, fun h => h, fun h => h⟩) $$ Hkl
  ihave %Hkls : ⌜kl.isSome⌝ $$ []
  · cases kl with
    | some _ => ipureintro; rfl
    | none =>
      iunfold klOk at Hkl
      icases Hkl with %H
      exact absurd Hrole H
  have Hterms_ok' : TermsOk terms (pappend s nw) := Hterms_ok
  have Hacks_term' : AcksTerm (pappend s nw) acks := Hacks_term
  have Hcamps_ok' : ∀ T, (camps !! T).isSome → uint.Z T ≤ uint.Z (pappend s nw).term := Hcamps_ok
  have Hwins_ok' : WinsOk wins (pappend s nw) := Hwins_ok
  ihave #Hrecs'' : logRecs γ (pappend s nw).base (pappend s nw).log $$ []
  · rw [show (pappend s nw).base = s.base from rfl, show (pappend s nw).log = s.log ++ nw from rfl]
    iexact Hrecs'
  ihave #Hbase'' : baseOk γ (pappend s nw).base $$ []
  · rw [show (pappend s nw).base = s.base from rfl]; iexact Hbase
  ihave #Hvlogs_ok' : vlogsOk γ (pappend s nw) acks vlogs $$ []
  · rw [show vlogsOk (GF := GF) γ (pappend s nw) acks vlogs = vlogsOk γ s acks vlogs from rfl]
    iexact Hvlogs_ok
  ihave Hevs' : ownEvs γ id (pappend s nw).term acks $$ [Hevs]
  · rw [show (pappend s nw).term = s.term from rfl]; iexact Hevs
  ihave #Hcmt' : isCommitted γ (cprefix fp (pappend s nw)) $$ []
  · rw [show cprefix fp (pappend s nw) = (fp ++ s.log ++ nw).take (uint.Z s.commit).toNat by
        simp only [cprefix, pappend, List.append_assoc]]
    rw [cprefix_app fp s nw (by
      have := Hfp.1
      unfold plogLastIndexZ at Hcl
      rw [List.length_append]; push_cast; omega)]
    iexact Hcmt
  ihave Hlg : ownLogGhost γ id (pappend s nw) kl $$ [Hterms Hacks Hcamps Hvlogs Htlog' Hwins Hevs']
  · unfold ownLogGhost
    iexists γm, terms, γa, acks, fp, γc, camps, γl, vlogs, γw, wins
    iframe % # ∗
  -- the self-acknowledgement
  ihave #Hl' : isLeader γ id (pappend s nw).term $$ []
  · rw [show (pappend s nw).term = s.term from rfl]; iexact Hl
  icases ownLogGhost_lead_full γ id (pappend s nw) kl Hrole $$ Hl' Hlg with
    ⟨⟨%fp', #Hp', #Hpf', -⟩, Hlg⟩
  ihave #HLf := leadFull_intro $$ Hp' Hpf'
  have HLs' : plogLastIndexZ (pappend s nw).base (pappend s nw).log = L + (ents.length : Int) := by
    show plogLastIndexZ s.base (s.log ++ nw) = _
    unfold plogLastIndexZ at HL ⊢
    rw [List.length_append, Hlen]; push_cast; omega
  have Hpl : uint.Z (plastIndex (pappend s nw)) = L + (ents.length : Int) := by
    unfold plastIndex; rw [HLs', uint_Z_W64 _ (by omega) (by omega)]
  imod ownLogGhost_ack γ id (pappend s nw) kl (plastIndex (pappend s nw)) $$ [] [] Hlg with
    ⟨Hlg, #Hack⟩
  · unfold ackOk
    iintro %_
    unfold ackAgree
    isplitr
    · ipureintro; show uint.Z (plastIndex (pappend s nw)) ≤ _; rw [Hpl, HLs']; exact Int.le_refl _
    iexists id, (pappend s nw).base, (pappend s nw).log
    isplitr
    · iexact Hp'
    isplitr
    · ipureintro
      refine ⟨plogTermAt_in_range _ _ _ ⟨?_, ?_⟩, rfl⟩
      · show uint.Z s.base.index' ≤ _; rw [Hpl]; omega
      · rw [Hpl, HLs']; exact Int.le_refl _
    · iexists fp'; iexact Hpf'
  · iintro %fp2 %Hf2 #Hfr2 -
    obtain ⟨Hf2, Hw2⟩ := Hf2
    icases lpfull_fp $$ Hpf' with ⟨#Hfr', %Hf'⟩
    ihave %Hfpeq := FullOk_unique γ (pappend s nw).base fp2 fp' Hf2 Hf'.1 $$ Hfr2 Hfr'
    subst Hfpeq
    icases leadFull_wf γ _ _ $$ HLf with ⟨%HwL, #HrL⟩
    iapply hist_of_agree γ (fp2 ++ (pappend s nw).log) (fp2 ++ (pappend s nw).log) _ _ _ HwL.1
      (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _,
        by rw [full_last_index _ _ _ Hf2, HLs', Hpl]; exact Int.le_refl _⟩) rfl $$ HrL
    unfold okL
    ileft
    iexists (pappend s nw).term
    isplitr
    · ipureintro
      refine ⟨Int.le_refl _, ?_⟩
      cases kl with
      | none => cases Hkls
      | some _ => show uint.Z s.term < uint.Z s.term + 1; omega
    · iexact HLf
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox, show (pappend s nw).outbox = s.outbox from rfl]
    iapply outbox_snoc $$ Hout
    unfold pselfAck
    iapply isMessage_appResp $$ Hack
  · iapply tally_eq γ id s _ (by rfl) (by rfl) $$ Htally
  · iapply leaderWit_eq γ id s _ (by rfl) (by rfl) $$ Hlead
  · iapply ownLogGhost_mono γ id (pappend s nw) _ kl (by rfl) (by rfl) (by rfl)
      (by intro h; exact ⟨h, rfl, rfl⟩) (by intro h; exact ⟨h, rfl⟩) (by exact fun h => h) (by rfl)
      (by exact fun h => h) $$ Hlg
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · lcm_mono
  · rd_mono

/-- `Step.snapStale`: back to follower of `m.src`, acknowledging the commit index --
`Step.appStale`'s update. -/
theorem ownRaftGhost_step_snap_stale (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) := by
  intro Hty Hfid Hterm Hrole
  exact ownRaftGhost_step_stale γ id s m (Or.inr Hty) Hfid Hterm Hrole

/-- `Step.snapFastfwd`: the new commit index is the snapshot's, which the message carries
the commit fact for and the log reaches (it has the snapshot's last entry, which the
leader's log has too). -/
theorem ownRaftGhost_step_snap_fastfwd (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit < uint.Z m.index →
    PlogMatches s.base s.log
      (entryID.mk m.logterm m.index) →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with commit := m.index }
           [Msg.mk .appResp id m.src s.term false m.index
              (W64 0) (W64 0) (W64 0) []]) := by
  intro Hty Hfid Hterm Hrole Hlt Hmt
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases isMessage_snap_inv γ m Hty $$ Hm with
    ⟨#Hl, -, ⟨%bL, %l', %fpL, #Hp', %Hidx', #Hpf', #Hmc, #Hmcm⟩, %Hfnz⟩
  rw [Hterm]
  iunfold isLeader at Hl
  icases Hl with ⟨%q, #Hwin⟩
  ihave %Hex := vote_excl γ id s γv voted m.src q Hname Hhist $$ Hvoted Hwin
  ihave Hlg := ownLogGhost_learn γ id s kl m.src q Hrole $$ Hwin %Hex Hlg
  ihave #HLf := leadFull_intro $$ Hp' Hpf'
  icases leadFull_wf γ s.term (fpL ++ l') $$ HLf with ⟨%HwLf, #HrLf⟩
  icases lpfull_fp $$ Hpf' with ⟨-, %HfL⟩
  have HbL := (plogTermAt_some_range _ _ _ _ Hidx').1
  have Hmt' : plogTermAt s.base s.log m.index = some m.logterm := Hmt
  have Hb := (plogTermAt_some_range _ _ _ _ Hmt').1
  have Hle := (plogTermAt_some_range _ _ _ _ Hmt').2
  have HFeq : ∀ fp, FullOk s.base fp →
      plogTermAt base0 (fp ++ s.log) m.index = plogTermAt base0 (fpL ++ l') m.index := by
    intro fp Hf
    rw [full_term_at s.base fp s.log m.index Hf Hb, full_term_at bL fpL l' m.index HfL.1 HbL,
      Hidx']
    exact Hmt'
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  ihave Hlg := ownLogGhost_mono' γ id s { padoptLeader s m.src with commit := m.index }
      (some m.src) (some m.src) rfl rfl (by intro h; cases h)
      (by intro _ h; exact absurd h Hrole) (by intro h; cases h) (Int.le_refl _)
      (by show uint.Z s.commit ≤ uint.Z m.index; omega)
      (Or.inl ⟨rfl, rfl, fun h => h, fun h => by cases h⟩) (Or.inr Hle)
      $$ Hlg [] [] []
  · iapply matchedOk_nonleader γ _ (by intro h; cases h)
  · iintro %fp % ⟨Hf, -⟩ - -
    simp only [padoptLeader]
    iapply commitIn_agree γ (fpL ++ l') (fp ++ s.log) m.index s.term s.term (Int.le_refl _)
      (HFeq fp Hf) $$ Hmc
  · iintro %fp % ⟨Hf, Hw⟩ #Hfr -
    simp only [cprefix, padoptLeader]
    ihave #HrF := logRecs_full γ s.base fp s.log Hf $$ Hfr Hrecs
    ihave %Htk := full_take_eq γ (fp ++ s.log) (fpL ++ l') m.index (full_wf _ _ _ Hf Hw) HwLf.1
      (by rw [full_term_at s.base fp s.log m.index Hf Hb, Hmt']; rfl) (HFeq fp Hf) $$ HrF HrLf
    rw [Htk]; iexact Hmcm
  imod ownLogGhost_ack γ id { padoptLeader s m.src with commit := m.index } (some m.src) m.index
    $$ [] [] Hlg with ⟨Hlg, #Hack⟩
  · unfold ackOk
    iintro %H
    exfalso; exact absurd H.2 (Int.lt_irrefl _)
  · iintro %fp % ⟨Hf, Hw⟩ #Hfr #Hc
    simp only [padoptLeader] at Hf Hw ⊢
    iapply hist_of_commit γ _ _ _ _ (full_wf _ _ _ Hf Hw)
      (by show uint.Z s.term < uint.Z s.term + 1; omega) $$ [] Hc
    iapply logRecs_full γ s.base fp s.log Hf $$ Hfr Hrecs
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted (some m.src) Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]; simp only [padoptLeader]
    iapply outbox_snoc $$ Hout
    iapply isMessage_appResp $$ Hack
  · iapply tally_empty γ id _ (by rfl)
  · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
  · iapply ownLogGhost_mono γ id { padoptLeader s m.src with commit := m.index } _ (some m.src)
      (by rfl) (by rfl) (by rfl)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by rfl) (by exact fun h => h)
      $$ Hlg
  · ipureintro; intro _; exact Hfid
  · ipureintro; intro _; rfl
  · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
  · lcm_mono
  · rd_mono

/-- `Step.snapRestore`: the log is replaced by the snapshot -- no entries after the new
base, so no records to keep; the compacted prefix is the leader's full log up to the
snapshot -- and the commit index becomes the snapshot's, which the message carries the
commit fact for. No justified acknowledgement of this term is above the snapshot: the
log would then agree with the leader at the snapshot's index (`ackAgree_term`), where
the leader has the snapshot's last entry -- but the rule's premise is that the log does
not have it. Histories move to the leader's log (`hist_replace`), which disagrees with
the old log at the snapshot's index. -/
theorem ownRaftGhost_step_snap_restore (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit < uint.Z m.index →
    ¬ PlogMatches s.base s.log
        (entryID.mk m.logterm m.index) →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with
               base := entryID.mk m.logterm m.index,
               log := [],
               commit := m.index }
           [Msg.mk .appResp id m.src s.term false m.index
              (W64 0) (W64 0) (W64 0) []]) := by
  intro Hty Hfid Hterm Hrole Hlt Hnm
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases isMessage_snap_inv γ m Hty $$ Hm with
    ⟨#Hl, #Hmeta, ⟨%bL, %l', %fpL, #Hp', %Hidx', #Hpf', #Hmc, #Hmcm⟩, %Hfnz⟩
  rw [Hterm]
  ihave #HLf := leadFull_intro $$ Hp' Hpf'
  icases leadFull_wf γ s.term (fpL ++ l') $$ HLf with ⟨%HwLf, #HrLf⟩
  icases lpfull_fp $$ Hpf' with ⟨-, %HfL⟩
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  obtain ⟨Hwf, Hbc, Hcl⟩ := Hok
  have HbL := (plogTermAt_some_range _ _ _ _ Hidx').1
  have HLidx : plogTermAt base0 (fpL ++ l') m.index = some m.logterm := by
    rw [full_term_at bL fpL l' m.index HfL.1 HbL]; exact Hidx'
  have Hfp' : FullOk (entryID.mk m.logterm m.index) ((fpL ++ l').take (uint.Z m.index).toNat) :=
    FullOk_take _ _ _ HwLf.1 HLidx
  have Hfp'j : ∀ j : w64, uint.Z j ≤ uint.Z m.index →
      plogTermAt base0 ((fpL ++ l').take (uint.Z m.index).toNat ++ []) j =
        plogTermAt base0 (fpL ++ l') j := by
    intro j Hj
    rw [List.append_nil]
    exact plogTermAt_take_full _ _ _ (by omega)
  have Hfp'last : plogLastIndexZ base0 ((fpL ++ l').take (uint.Z m.index).toNat ++ []) =
      uint.Z m.index := by
    unfold plogLastIndexZ; rw [List.append_nil, base0_index, Hfp'.1]; simp
  -- learn the leader
  iunfold isLeader at Hl
  icases Hl with ⟨%q, #Hwin⟩
  ihave %Hex := vote_excl γ id s γv voted m.src q Hname Hhist $$ Hvoted Hwin
  ihave Hlg := ownLogGhost_learn γ id s kl m.src q Hrole $$ Hwin %Hex Hlg
  have Hbase_le : uint.Z s.base.index' ≤ uint.Z m.index := by omega
  ihave Hlg := ownLogGhost_upd γ id s
      { padoptLeader s m.src with
          base := entryID.mk m.logterm m.index, log := [], commit := m.index }
      (some m.src) (some m.src)
      (by intro h; cases h) (by intro _ h; exact absurd h Hrole) (by intro h; cases h)
      (Int.le_refl _) (by show uint.Z s.commit ≤ uint.Z m.index; omega)
      (Or.inl ⟨rfl, rfl, fun h => h, fun h => by cases h⟩)
      ⟨fun k e Hk => by simp at Hk, Int.le_refl _,
        by show uint.Z m.index ≤ uint.Z m.index + (([] : List raftpb.Entry).length : Int); simp⟩
      $$ Hlg [] [] [] [Hmeta] []
  · imodintro
    iintro - %i %Hi #Ha
    ihave %Hj := ackAgree_term γ s.base s.log s.term i m.src bL l' m.index Hwf Hbase_le HbL
      (by show uint.Z m.index ≤ uint.Z i; exact Int.le_of_lt Hi) (by rw [Hidx']; rfl) $$ Hrecs Ha Hp'
    exfalso
    exact Hnm (Hj.trans Hidx')
  · unfold logRecs
    iapply BigSepL.bigSepL_nil.2; iempintro
  · iapply matchedOk_nonleader γ _ (by intro h; cases h)
  · unfold baseOk; iright; iexact Hmeta
  · iintro %fp %Hf3 #Hfr #Hc -
    obtain ⟨Hf, Hw, Htle⟩ := Hf3
    iexists (fpL ++ l').take (uint.Z m.index).toNat
    isplitr
    · ipureintro
      refine ⟨⟨Hfp', fun k e Hk => by simp at Hk, ?_⟩, fun Hr => absurd rfl Hr⟩
      intro j x Hx
      refine ⟨?_, fun h => by cases h⟩
      have Hjr := (plogTermAt_some_range _ _ _ _ Hx).2
      rw [Hfp'last] at Hjr
      have Hx' : plogTermAt base0 ((fpL ++ l').take (uint.Z m.index).toNat ++ []) j = some x := Hx
      rw [Hfp'j j Hjr] at Hx'
      exact HwLf.2 j x Hx'
    isplitr
    · iapply logRecs_take $$ HrLf
    isplitr
    · simp only [padoptLeader]
      iapply commitIn_agree γ (fpL ++ l') _ m.index s.term s.term (Int.le_refl _)
        (Hfp'j m.index (Int.le_refl _)) $$ Hmc
    isplitr
    · simp only [cprefix, List.append_nil, List.take_take, Nat.min_self]
      iexact Hmcm
    · imodintro
      iintro %t %i %Ht #Hh
      simp only [bnd, padoptLeader]
      iapply hist_replace γ (fp ++ s.log) ((fpL ++ l').take (uint.Z m.index).toNat ++ []) (fpL ++ l')
        t i s.term (uint.Z s.term + 1) (uint.Z s.term + 1) 1 m.index m.index
        (Int.le_refl _) Ht (by show uint.Z s.term < uint.Z s.term + 1; omega)
        (by have := uint_Z_nonneg s.commit; omega)
        ⟨by have := uint_Z_nonneg s.commit; omega, Int.le_refl _⟩
        ?_ ?_ ?_ ?_ $$ HLf Hh
      · intro j Hj
        have Hj0 : uint.Z j = 0 := by have := uint_Z_nonneg j; omega
        simp only [plogTermAt, base0_index, Hj0, Int.lt_irrefl, ↓reduceIte]
      · intro j Hj
        refine ⟨Hfp'j j Hj.2, ?_⟩
        exact full_term_at_some (fpL ++ l') j m.index (by rw [HLidx]; rfl) Hj.2
      · rw [HLidx, full_term_at s.base fp s.log m.index Hf Hbase_le]
        exact fun h => Hnm h
      · intro j Hj
        exact (plogTermAt_none_range _ _ _).mpr (Or.inr (by rw [Hfp'last]; exact Hj))
  imod ownLogGhost_ack γ id
      { padoptLeader s m.src with
          base := entryID.mk m.logterm m.index, log := [], commit := m.index }
      (some m.src) m.index $$ [] [] Hlg with ⟨Hlg, #Hack⟩
  · unfold ackOk
    iintro %H
    exfalso; exact absurd H.2 (Int.lt_irrefl _)
  · iintro %fp %Hf2 #Hfr #Hc
    obtain ⟨Hf, Hw⟩ := Hf2
    iapply hist_of_commit γ _ _ _ _ (full_wf _ _ _ Hf Hw)
      (by show uint.Z s.term < uint.Z s.term + 1; omega) $$ [] Hc
    iapply logRecs_full γ _ fp [] Hf $$ Hfr []
    unfold logRecs
    iapply BigSepL.bigSepL_nil.2; iempintro
  imodintro
  iapply ownRaftGhost_intro γ id _ γv voted (some m.src) Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
  · ipureintro; exact Hhist
  · rw [psendMsgs_outbox]; simp only [padoptLeader]
    iapply outbox_snoc $$ Hout
    iapply isMessage_appResp $$ Hack
  · iapply tally_empty γ id _ (by rfl)
  · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
  · iapply ownLogGhost_mono γ id
      { padoptLeader s m.src with
          base := entryID.mk m.logterm m.index, log := [], commit := m.index } _ (some m.src)
      (by rfl) (by rfl) (by rfl)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by rfl) (by exact fun h => h)
      $$ Hlg
  · ipureintro; intro _; exact Hfid
  · ipureintro; intro _; rfl
  · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
  · lcm_mono
  · rd_mono

/-! ### The refinement obligation -/

theorem ownRaftGhost_step (γ : RaftNames) (id : w64) (s : PState) (recv : List Msg)
    (s' : PState) :
    Step γ.reCfg id s recv s' →
    ⊢ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗
      ownRaftGhost γ id s ={⊤}=∗
      ownRaftGhost γ id s' := by
  intro Hstep
  induction Hstep with
  | refl s =>
    iintro _ Hown
    imodintro; iexact Hown
  | trans s0 r1 s1 r2 s2 _ _ IH1 IH2 =>
    iintro Hrecv Hown
    icases (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ Hrecv with
      ⟨Hr1, Hr2⟩
    imod IH1 $$ Hr1 Hown with Hown
    iapply IH2 $$ Hr2 Hown
  | higherTerm m s Hlt Hto Hfl =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    have Hne : m.term ≠ s.term := by intro Heq; rw [Heq] at Hlt; omega
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted none Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro
      refine ⟨fun t Ht => ?_, ?_⟩
      · have := Hhist.1 t Ht; show uint.Z t ≤ uint.Z m.term; omega
      · rw [pbecomeFollower_vote_ne s _ _ Hne]
        simp only [pbecomeFollower, ↓reduceIte]
        exact vote_hist_fresh voted s m.term Hhist Hlt
    · iapply outbox_eq γ s _ (by rfl) $$ Hout
    · iapply tally_empty γ id _ (by rfl)
    · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
    · iapply ownLogGhost_mono_up γ id s _ kl (by rfl) (by rfl) (by rfl) (by rfl) (by exact Hlt) $$ Hlg
    · ipureintro; intro _
      show (if fromLeader m.ty then m.src else W64 0) ≠ id
      split
      · rename_i h; exact Hfl h
      · exact fun h => Hidnz h.symm
    · ipureintro; intro _; rfl
    · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
    · lcm_mono
    · rd_mono
  | campaign s peers Hrole Hin Hnw Hperm =>
    have Hcnt : rdCount ([Msg.plain .voteResp id id (pbecomeCandidate id s).term false] ++
        List.map (fun dst => pvoteReq id dst (pbecomeCandidate id s).term (plogLast s.base s.log))
          peers) = 0 := by
      rw [rdCount_append, rdCount_singleton]
      unfold rdCount
      simp [List.countP_eq_zero, pvoteReq, Msg.plain]
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    ihave #Hinv := ownLogGhost_inv $$ Hlg
    imod ownLogGhost_campaign γ id s kl Hrole Hnw $$ Hlg with
      ⟨%kv, %F, Hlg, #Hcamp, #Hvl, #HrF, %HF, #Hvev⟩
    have Ht' : uint.Z (s.term + W64 1) = uint.Z s.term + 1 := by word
    have Hfree : voted !! (s.term + W64 1) = none :=
      vote_hist_fresh voted s _ Hhist (by omega)
    ihave #Hvj : voteJust γ id (s.term + W64 1) id $$ []
    · unfold voteJust
      iexists kv, false, F, F
      iframe Hvl Hcamp HrF Hvev
      isplitr
      · ipureintro
        refine ⟨HF.1, ?_⟩
        simp [plogUpToDate]
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    imod vote_insert γ id γv voted (s.term + W64 1) id Hname Hfree $$ Hinv Hvj Hvoted with
      ⟨Hvoted, #Hself⟩
    ihave #Hisvote : isVote γ id (s.term + W64 1) id $$ []
    · unfold isVote; iexists γv; iframe Hself; ipureintro; exact Hname
    imodintro
    iapply ownRaftGhost_intro γ id _ γv (<[s.term + W64 1 := id]> voted) none Hname Hidnz $$
      Hvoted [] [] [] [] [] [Hlg] [] [] [] [] [Hlcm] [Hrd]
    · ipureintro
      refine ⟨fun t Ht => ?_, ?_⟩
      · show uint.Z t ≤ uint.Z (s.term + W64 1)
        by_cases htt : t = s.term + W64 1
        · subst htt; omega
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm htt)] at Ht
          have := Hhist.1 t Ht; omega
      · show (<[s.term + W64 1 := id]> voted) !! (s.term + W64 1) =
          (if id = W64 0 then none else some id)
        rw [GMap.lookup_insert_eq]; simp only [Hidnz, ↓reduceIte]
    · iapply (BigSepM.bigSepM_insert (Φ := fun t c => isVote (GF := GF) γ id t c) Hfree).2
      isplitr
      · iexact Hisvote
      · iexact Hfrags
    · rw [psendMsgs_outbox]; simp only [pbecomeCandidate]
      iapply outbox_app $$ Hout
      iapply outbox_app
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
        iapply isMessage_grant γ id id _ $$ Hisvote
      · iapply BigSepL.bigSepL_forall_elim
        iintro %k %x %Hk
        rw [List.getElem?_map] at Hk
        cases Hd : peers[k]? with
        | none => rw [Hd] at Hk; cases Hk
        | some dst =>
          rw [Hd] at Hk; cases Hk
          iapply isMessage_voteReq γ id dst _ _ F HF.2 $$ Hcamp
    · iapply tally_empty γ id _ (by rfl)
    · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
    · iapply ownLogGhost_mono γ id (pbecomeCandidate id s) _ none (by rfl) (by rfl) (by rfl)
        (by intro h; cases h) (by intro h; exact ⟨h, rfl⟩) (by intro h; cases h) (by rfl)
        (by exact fun h => h) $$ Hlg
    · ipureintro; intro _; exact fun h => Hidnz h.symm
    · ipureintro; intro h; cases h
    · iapply (BigSepM.bigSepM_insert (Φ := fun t c => voteJust (GF := GF) γ id t c) Hfree).2
      isplitr
      · iexact Hvj
      · iexact Hvrecs
    · ipureintro; exact ⟨fun _ => rfl, fun _ => rfl⟩
    · lcm_mono
    · iapply rdOwn_mono _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $$ Hrd <;>
        first
          | (rw [psendMsgs_outbox, rdCount_append, Hcnt]; simp [pbecomeCandidate]; done)
          | (intro h; simp_all [psendMsgs, pbecomeCandidate]; done)
          | (intro h; simp [psendMsgs, pbecomeCandidate, rdNL])
          | (intro h h'; simp_all [psendMsgs, pbecomeCandidate]; done)
          | (simp [psendMsgs, pbecomeCandidate]; omega)
          | (dsimp only [psendMsgs, pbecomeCandidate]; word)
          | rfl
  | grantVote m s Hty Hto Hfrom Hterm Hcan Hutd =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    icases isMessage_vote_inv γ m Hty $$ Hm with ⟨%Fc, #Hcamp, %HFc⟩
    rw [Hterm]
    ihave #Hinv := ownLogGhost_inv $$ Hlg
    ihave H2 : |={⊤}=> ∃ voted', ghostMapAuth γv (1 : Qp).half voted' ∗
        ⌜VoteHistOk voted' { s with vote := m.src }⌝ ∗
        ([∗map] t ↦ c ∈ voted', isVote γ id t c) ∗
        ([∗map] t ↦ c ∈ voted', voteJust γ id t c) ∗
        isVote γ id s.term m.src ∗ ownLogGhost γ id s kl $$ [Hvoted Hlg]
    · rcases Hcan with Hsame | ⟨Hnovote, Hnolead⟩
      · have Hvnz : s.vote ≠ W64 0 := by rw [Hsame]; exact Hfrom
        have Hlook : voted !! s.term = some m.src := by
          rw [Hhist.2, Hsame]; simp only [Hfrom, ↓reduceIte]
        ihave #Hone := BigSepM.bigSepM_lookup (Φ := fun t c => isVote (GF := GF) γ id t c) Hlook $$ Hfrags
        imodintro
        iexists voted
        iframe Hvoted Hfrags Hvrecs Hone Hlg
        ipureintro
        exact ⟨Hhist.1, by show voted !! s.term = _; rw [Hhist.2, ← Hsame]⟩
      · have Hfree : voted !! s.term = none := by
          rw [Hhist.2]; simp only [Hnovote, ↓reduceIte]
        imod ownLogGhost_vote γ id s kl $$ Hlg with
          ⟨%kv, %Fv, Hlg, #Hvl, #HrFv, #Hklv, %HFv, #Hvev⟩
        ihave #Hvj : voteJust γ id s.term m.src $$ []
        · unfold voteJust
          iexists kv, kl.isSome, Fv, Fc
          isplitr; · iexact Hvl
          isplitr; · iexact Hcamp
          isplitr; · iexact HrFv
          isplitr
          · ipureintro; exact ⟨HFv.1, by rw [HFv.2, HFc]; exact Hutd⟩
          isplitr
          · cases kl with
            | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; itrivial
            | some ldr =>
              simp only [Option.isSome_some, ↓reduceIte]
              iunfold klOk at Hklv
              icases Hklv with ⟨⟨%qw, #Hw, %Hq⟩, -⟩
              iexists ldr, qw
              iframe Hw
              ipureintro; exact Hq Hnovote
          · iexact Hvev
        imod vote_insert γ id γv voted s.term m.src Hname Hfree $$ Hinv Hvj Hvoted with
          ⟨Hvoted, #Hnew⟩
        ihave #Hisvote : isVote γ id s.term m.src $$ []
        · unfold isVote; iexists γv; iframe Hnew; ipureintro; exact Hname
        imodintro
        iexists <[s.term := m.src]> voted
        iframe Hvoted Hisvote Hlg
        isplitr
        · ipureintro
          refine ⟨fun t Ht => ?_, ?_⟩
          · show uint.Z t ≤ uint.Z s.term
            by_cases htt : t = s.term
            · subst htt; exact Int.le_refl _
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm htt)] at Ht; exact Hhist.1 t Ht
          · show (<[s.term := m.src]> voted) !! s.term = (if m.src = W64 0 then none else some m.src)
            rw [GMap.lookup_insert_eq]; simp only [Hfrom, ↓reduceIte]
        isplitr
        · iapply (BigSepM.bigSepM_insert (Φ := fun t c => isVote (GF := GF) γ id t c) Hfree).2
          isplitr
          · iexact Hisvote
          · iexact Hfrags
        · iapply (BigSepM.bigSepM_insert (Φ := fun t c => voteJust (GF := GF) γ id t c) Hfree).2
          isplitr
          · iexact Hvj
          · iexact Hvrecs
    imod H2 with ⟨%voted', Hvoted, %Hhist', #Hfrags', #Hvrecs', #Hgrant, Hlg⟩
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted' kl Hname Hidnz $$ Hvoted [] Hfrags' [] [] [] [Hlg] [] [] Hvrecs' [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist'
    · rw [psendMsgs_outbox]
      iapply outbox_snoc $$ Hout
      iapply isMessage_grant $$ Hgrant
    · iapply tally_eq γ id s _ (by rfl) (by rfl) $$ Htally
    · iapply leaderWit_eq γ id s _ (by rfl) (by rfl) $$ Hlead
    · iapply ownLogGhost_mono γ id s _ kl (by rfl) (by rfl) (by rfl)
        (by intro h; exact ⟨h, rfl, rfl⟩) (by intro h; exact ⟨h, rfl⟩) (by exact fun h => h) (by rfl)
        (by intro h; exact absurd h Hfrom) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; exact Hfollower_votes
    · ipureintro
      refine ⟨fun Hr => ?_, Hrole_ok.2⟩
      show m.src = id
      rcases Hcan with Hs | ⟨Hn, -⟩
      · rw [← Hs]; exact Hrole_ok.1 Hr
      · exfalso; apply Hidnz; rw [← Hn]; exact (Hrole_ok.1 Hr).symm
    · lcm_mono
    · rd_mono
  | rejectVote m s Hty Hto =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist
    · rw [psendMsgs_outbox]
      iapply outbox_snoc $$ Hout
      iapply isMessage_reject
    · iapply tally_eq γ id s (psendMsgs s _) rfl rfl $$ Htally
    · iapply leaderWit_eq γ id s (psendMsgs s _) rfl rfl $$ Hlead
    · iapply ownLogGhost_mono γ id s (psendMsgs s _) kl rfl rfl rfl (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; exact Hfollower_votes
    · ipureintro; exact Hrole_ok
    · lcm_mono
    · rd_mono
  | recordVote m s Hty Hto Hterm Hrole =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist
    · iexact Hout
    · iapply BigSepM.bigSepM_forall_elim
      iintro %v %u %Hv
      have Hv' : v ∈ granted (recordVote s.votes m.src (!m.reject)) :=
        (GMap.elem_of_gset _ _).mpr (by cases u; exact Hv)
      rcases elem_of_granted_recordVote _ _ _ _ Hv' with Hv'' | ⟨rfl, Hb⟩
      · iapply BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v s.term id)
          ((GMap.elem_of_gset _ _).mp Hv'') $$ Htally
      · have Hrej : m.reject = false := by cases h : m.reject <;> simp_all
        ihave #Hg := isMessage_grant_inv γ m Hty Hrej $$ Hm
        rw [Hterm, Hto] at *
        iexact Hg
    · iapply leaderWit_eq γ id s _ (by rfl) (by rfl) $$ Hlead
    · iapply ownLogGhost_mono γ id s _ kl (by rfl) (by rfl) (by rfl)
        (by intro h; exact ⟨h, rfl, rfl⟩) (by intro h; exact ⟨h, rfl⟩) (by exact fun h => h) (by rfl)
        (by exact fun h => h) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; intro h; rw [Hrole] at h; cases h
    · ipureintro; exact Hrole_ok
    · lcm_mono
    · rd_mono
  | win s mt ms Hrole Hq Hnw Hmt Hms =>
    iintro _ Hown
    imod ownRaftGhost_step_win γ id s mt ms Hrole Hq Hnw Hmt Hms $$ Hown with Hown
    imodintro; iexact Hown
  | lose s Hrole Hnq =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    have Hlead0 := Hrole_ok.2 Hrole
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro
      exact VoteHistOk_eq voted s _ Hhist rfl (pbecomeFollower_vote_same s _)
    · iapply outbox_eq γ s _ (by rfl) $$ Hout
    · iapply tally_empty γ id _ (by rfl)
    · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
    · iapply ownLogGhost_mono γ id s _ kl (by rfl) (by rfl) (by rfl)
        (by intro h; cases h) (by intro h; cases h) (by intro h; rw [Hrole] at h; cases h) (by rfl)
        (by intro h; rw [← pbecomeFollower_vote_same s (W64 0)]; exact h) $$ Hlg
    · ipureintro; intro _; exact fun h => Hidnz h.symm
    · ipureintro; intro _; rfl
    · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
    · lcm_mono
    · rd_mono
  | drain s o' Hsub =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist
    · iapply BigSepL.bigSepL_forall_elim
      iintro %k %x %Hk
      obtain ⟨j, Hj⟩ := List.mem_iff_getElem?.mp (Hsub.subset (List.mem_of_getElem? Hk))
      iapply BigSepL.bigSepL_lookup (Φ := fun _ m => isMessage (GF := GF) γ m) Hj $$ Hout
    · iexact Htally
    · iapply leaderWit_eq γ id s _ (by rfl) (by rfl) $$ Hlead
    · iapply ownLogGhost_mono γ id s _ kl (by rfl) (by rfl) (by rfl)
        (by intro h; exact ⟨h, rfl, rfl⟩) (by intro h; exact ⟨h, rfl⟩) (by exact fun h => h) (by rfl)
        (by exact fun h => h) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; exact Hfollower_votes
    · ipureintro; exact Hrole_ok
    · lcm_mono
    · rd_mono
  | appAccept m s lastnewi es' Hty _ Hfid Hterm Hrole Hcm Happ _ =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_app_accept γ id s m lastnewi es' Hty Hfid Hterm Hrole Hcm Happ $$ Hm Hown with Hown
    imodintro; iexact Hown
  | appStale m s Hty _ Hfid Hterm Hrole _ =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_app_stale γ id s m Hty Hfid Hterm Hrole $$ Hm Hown with Hown
    imodintro; iexact Hown
  | appReject m s hint hintterm Hty _ Hfid _ Hrole _ _ =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_app_reject γ id s m hint hintterm Hty Hfid Hrole $$ Hm Hown with Hown
    imodintro; iexact Hown
  | heartbeat m s Hty Hto Hfid Hterm Hrole Hcm =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_heartbeat γ id s m Hty Hto Hterm Hfid Hrole Hcm $$ Hm Hown with Hown
    imodintro; iexact Hown
  | beat s ms Hrole Hms Hctx =>
    iintro _ Hown
    imod ownRaftGhost_step_beat γ id s ms Hrole Hms Hctx $$ Hown with Hown
    imodintro; iexact Hown
  | appResp m s x Hty _ Hterm Hrole Hrej Hx =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_app_resp γ id s m x Hty Hterm Hrole Hrej Hx $$ Hm Hown with Hown
    imodintro; iexact Hown
  | commit s n Hrole Hlt Hle Htm Hq =>
    iintro _ Hown
    iapply ownRaftGhost_step_commit γ id s n Hrole Hlt Hle Htm Hq $$ Hown
  | sendApps s ms Hrole Hms =>
    iintro _ Hown
    imod ownRaftGhost_step_send_apps γ id s ms Hrole Hms $$ Hown with Hown
    imodintro; iexact Hown
  | propose m s ents Hty Hents Hrole _ Hnw =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    iunfold isMessage at Hm
    rw [Hty]
    icases Hm with ⟨-, #Hed⟩
    rw [Hents]
    imod ownRaftGhost_step_propose γ id s ents Hrole Hnw $$ Hed Hown with Hown
    imodintro; iexact Hown
  | propForward m s Hty _ _ =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_prop_forward γ id s m Hty $$ Hm Hown with Hown
    imodintro; iexact Hown
  | snapRestore m s Hty _ Hfid Hterm Hrole _ _ Hlt Hnm =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_snap_restore γ id s m Hty Hfid Hterm Hrole Hlt Hnm $$ Hm Hown with Hown
    imodintro; iexact Hown
  | snapFastfwd m s Hty _ Hfid Hterm Hrole _ _ Hlt Hmt =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_snap_fastfwd γ id s m Hty Hfid Hterm Hrole Hlt Hmt $$ Hm Hown with Hown
    imodintro; iexact Hown
  | snapStale m s Hty _ Hfid Hterm Hrole _ =>
    iintro Hrecv Hown
    ihave #Hm := recv_one $$ Hrecv
    imod ownRaftGhost_step_snap_stale γ id s m Hty Hfid Hterm Hrole $$ Hm Hown with Hown
    imodintro; iexact Hown
  | takeReads s =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    icases rdOwn_takeReads γ id s $$ Hrd with ⟨Hrd, -⟩
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist
    · iapply outbox_eq γ s _ (by rfl) $$ Hout
    · iapply tally_eq γ id s _ rfl rfl $$ Htally
    · iapply leaderWit_eq γ id s { s with rd := { s.rd with states := [] } } rfl rfl $$ Hlead
    · iapply ownLogGhost_mono γ id s { s with rd := { s.rd with states := [] } } kl rfl rfl rfl
        (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; exact Hfollower_votes
    · ipureintro; exact Hrole_ok
    · lcm_mono
    · iexact Hrd
  | sendFree s m Hfree Hfrom =>
    have Hcnt : rdCount [m] = 0 := by
      rw [rdCount_singleton]; rcases Hfree with h | h <;> simp [h]
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist
    · rw [psendMsgs_outbox]
      iapply outbox_snoc $$ Hout
      iapply isMessage_free
      rcases Hfree with h | h <;> rw [h] <;> rfl
    · iapply tally_eq γ id s (psendMsgs s _) rfl rfl $$ Htally
    · iapply leaderWit_eq γ id s (psendMsgs s _) rfl rfl $$ Hlead
    · iapply ownLogGhost_mono γ id s (psendMsgs s _) kl rfl rfl rfl (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; exact Hfollower_votes
    · ipureintro; exact Hrole_ok
    · lcm_mono
    · rd_mono
  | abandon s Hrole =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro
      exact VoteHistOk_eq voted s _ Hhist rfl (pbecomeFollower_vote_same s _)
    · iapply outbox_eq γ s _ (by rfl) $$ Hout
    · iapply tally_empty γ id _ (by rfl)
    · iapply leaderWit_nonleader γ id _ (by intro h; cases h)
    · iapply ownLogGhost_mono γ id s _ kl (by rfl) (by rfl) (by rfl)
        (by intro h; cases h) (by intro h; cases h) (by intro h; exact absurd h Hrole) (by rfl)
        (by intro h; rw [← pbecomeFollower_vote_same s (W64 0)]; exact h) $$ Hlg
    · ipureintro; intro _; exact fun h => Hidnz h.symm
    · ipureintro; intro _; rfl
    · ipureintro; exact ⟨fun h => absurd rfl h, fun h => by cases h⟩
    · lcm_mono
    · rd_mono
  | zeroAck s dst =>
    iintro _ Hown
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    imodintro
    iapply ownRaftGhost_intro γ id _ γv voted kl Hname Hidnz $$ Hvoted [] Hfrags [] [] [] [Hlg] [] [] Hvrecs [] [Hlcm] [Hrd]
    · ipureintro; exact Hhist
    · rw [psendMsgs_outbox]
      iapply outbox_snoc $$ Hout
      iapply isMessage_appResp
      unfold isAcked; ileft; ipureintro; rfl
    · iapply tally_eq γ id s (psendMsgs s _) rfl rfl $$ Htally
    · iapply leaderWit_eq γ id s (psendMsgs s _) rfl rfl $$ Hlead
    · iapply ownLogGhost_mono γ id s (psendMsgs s _) kl rfl rfl rfl (fun h => ⟨h, rfl, rfl⟩) (fun h => ⟨h, rfl⟩) (fun h => h) rfl (fun h => h) $$ Hlg
    · ipureintro; exact Hlead_ok
    · ipureintro; exact Hfollower_votes
    · ipureintro; exact Hrole_ok
    · lcm_mono
    · rd_mono

end ghost

end EtcdGrove
end Perennial
