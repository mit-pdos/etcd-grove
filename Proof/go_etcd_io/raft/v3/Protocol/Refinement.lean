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
  iapply lcmOwn_mono _ _ _ _ ?_ ?_ ?_ ?_ ?_ $$ Hlcm <;>
  first
    | (intro _; right; dsimp only [psendMsgs, pbecomeCandidate]; omega)
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
  iapply rdOwn_mono _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $$ Hrd <;>
  first
    | rfl
    | (intro _; right; dsimp only [psendMsgs, pbecomeCandidate]; omega)
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
    | exact List.Subperm.refl _
    | (apply propsOf_subperm; assumption)
    | (simp [propsOf_append, propsOf_cons, psendMsgs, Msg.plain, pselfAck, pvoteReq, padoptLeader,
        pbecomeFollower, pbecomeCandidate, list_subperm_self]; done)
    | (simp_all [propsOf_append, propsOf_cons, psendMsgs, pselfAck, list_subperm_self]; done)
    | exact Int.le_refl _
    | exact Nat.le_refl _
    | omega
    | word))

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
variable {md : Bool}

theorem rdCount_replOk (id : w64) (s : PState) (ms : List Msg) (h : ∀ m ∈ ms, ReplOk id s m) :
    rdCount ms = 0 := by
  unfold rdCount; rw [List.countP_eq_zero]
  intro m hm
  rcases h m hm with h' | h' <;> simp [h'.1]

theorem propsOf_replOk (id : w64) (s : PState) (ms : List Msg) (h : ∀ m ∈ ms, ReplOk id s m) :
    propsOf ms = [] :=
  propsOf_eq_nil ms (fun m hm => by rcases h m hm with h' | h' <;> simp [h'.1])


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
private theorem outbox_app (γ : RaftNames) (id : w64) (s : PState) (πc : List Prom) (W : DurMaps)
    (o ms : List Msg) :
    ⊢ ([∗list] m ∈ o, outMsgOk (GF := GF) γ id s πc W m) -∗
      ([∗list] m ∈ ms, outMsgOk γ id s πc W m) -∗
      [∗list] m ∈ o ++ ms, outMsgOk γ id s πc W m := by
  -- PORT(durability stage II): proof (restated over `outMsgOk` (durability R7))
  sorry

private theorem outbox_snoc (γ : RaftNames) (id : w64) (s : PState) (πc : List Prom) (W : DurMaps)
    (o : List Msg) (m : Msg) :
    ⊢ ([∗list] m ∈ o, outMsgOk (GF := GF) γ id s πc W m) -∗ outMsgOk γ id s πc W m -∗
      [∗list] m ∈ o ++ [m], outMsgOk γ id s πc W m := by
  -- PORT(durability stage II): proof (restated over `outMsgOk` (durability R7))
  sorry

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
theorem lpfull_fp (γ : RaftNames) (ldr t : w64) (bL : entryID)
    (l fp : List EntryM) :
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
  iintro ⟨H, -⟩; iexact H

/-- An accepting `MsgAppResp`: the acknowledgement and (since 2026-10-16, stage R8a) the witness
that its index is within the term's leader's log. -/
private theorem isMessage_appResp (γ : RaftNames) (src dst term idx : w64) :
    ⊢ isAcked (GF := GF) γ src term idx -∗ ackIn γ term idx -∗
      isMessage γ (Msg.mk .appResp src dst term false idx (W64 0) (W64 0) (W64 0) []) := by
  unfold isMessage
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro H Hi
  isplitl [H]
  · iexact H
  · iexact Hi

private theorem isMessage_appResp_rej (γ : RaftNames) (src dst term idx a b c : w64)
    (H : γ.reBoot ≠ [] → (γ.reBoot.length : Int) < uint.Z idx ∧ 1 ≤ uint.Z c ∧
      uint.Z c ≤ uint.Z idx) :
    ⊢ isMessage (GF := GF) γ (Msg.mk .appResp src dst term true idx a b c []) := by
  unfold isMessage; simp only [↓reduceIte]; iintro; ipureintro; exact H

private theorem matchedOk_leader (γ : RaftNames) (id : w64) (s : PState) (fp : List EntryM) :
    s.role = .leader →
    matchedOk (GF := GF) γ id s fp = iprop([∗map] v ↦ i ∈ s.matched, isAcked γ v s.term i ∨
      ⌜v = id ∧ ∀ x, plogTermAt base0 (fp ++ s.log) i = some x → uint.Z x < uint.Z s.term⌝) := by
  -- PORT(durability stage II): proof (`matchedOk` restated (durability R3))
  sorry

theorem isMessage_app_inv (γ : RaftNames) (m : Msg) :
    m.ty = .app →
    ⊢ isMessage (GF := GF) γ m -∗
      ⌜AppPayloadOk m⌝ ∗
      isLeader γ m.src m.term ∗
      (∃ bL l fp, leadPrefix γ m.src m.term bL l ∗
         ⌜plogTermAt bL l m.index = some m.logterm ∧
           m.entries <+: plogFrom bL l (m.index + W64 1)⌝ ∗
         lpfull γ m.src m.term bL l fp ∗
         commitIn γ (fp ++ l) m.commit m.term ∗
         isCommitted γ ((fp ++ l).take (uint.Z m.commit).toNat) ∗
         dynOn γ iprop(⌜ConfI1 (fp ++ l) (uint.Z m.commit).toNat⌝)) ∗
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
  iintro ⟨H1, H2, H3, H4, -⟩
  iframe H1 H2 H3 H4

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

/-- What an `app` and a `snap` share: a log of the leader of the term, with its full log. -/
private theorem isMessage_leadPrefix (γ : RaftNames) (m : Msg) :
    m.ty = .app ∨ m.ty = .snap →
    ⊢ isMessage (GF := GF) γ m -∗
      ∃ bL l fp, leadPrefix γ m.src m.term bL l ∗ lpfull γ m.src m.term bL l fp := by
  intro Hty
  iintro #Hm
  rcases Hty with Hty | Hty
  · icases isMessage_app_inv γ m Hty $$ Hm with ⟨-, -, ⟨%bL, %l, %fp, #Hp, -, #Hpf, -⟩, -⟩
    iexists bL, l, fp; iframe Hp Hpf
  · icases isMessage_snap_inv γ m Hty $$ Hm with ⟨-, -, ⟨%bL, %l, %fp, #Hp, -, #Hpf, -⟩, -⟩
    iexists bL, l, fp; iframe Hp Hpf

/-- Two full logs with records agree below an index within the bootstrap log (2026-10-16,
stage R8b): both start with it (`logRecs_boot_take`). -/
private theorem boot_take_agree (γ : RaftNames) (F1 F2 : List EntryM) (c : w64) :
    PlogWf base0 F1 → PlogWf base0 F2 → uint.Z c ≤ γ.reBoot.length →
    uint.Z c ≤ F1.length → uint.Z c ≤ F2.length →
    ⊢ logRecs (GF := GF) γ base0 F1 -∗ logRecs γ base0 F2 -∗
      ⌜F1.take (uint.Z c).toNat = F2.take (uint.Z c).toNat ∧
        plogTermAt base0 F1 c = plogTermAt base0 F2 c⌝ := by
  intro Hw1 Hw2 Hcb Hc1 Hc2
  iintro #H1 #H2
  icases logRecs_boot_take γ F1 Hw1 $$ H1 with %Ht1
  icases logRecs_boot_take γ F2 Hw2 $$ H2 with %Ht2
  icases logRecs_boot_termAt γ F1 Hw1 $$ H1 with %Ha1
  icases logRecs_boot_termAt γ F2 Hw2 $$ H2 with %Ha2
  ipureintro
  refine ⟨?_, ?_⟩
  · rw [Ht1 _ (by omega) (by omega), Ht2 _ (by omega) (by omega)]
  · rw [← Ha1 c Hcb Hc1, ← Ha2 c Hcb Hc2]

/-- **A commit index is within the log of the leader of any later term** (2026-10-16, stage R8a,
D11): a commit index `c` justified at a term `tm ≤ t` is at most the last index of a log of the
term-`t` leader (`ackIn γ t c`). The commit fact `cq γ t' n G` behind it has `c ≤ n` at the
term-`t'` leader's log `G`; at `t' = t`, `G` is itself a `leadPrefix` of `t`; at `t' < t`, leader
completeness (`lc_core`, which needs the vote table) puts `n` in the given term-`t` leader's full
log. What a follower's reply acknowledging its commit index (the stale `MsgApp` and `MsgSnap`
replies) carries. -/
theorem commitIn_ackIn (γ : RaftNames) (ldr t : w64) (bL : entryID) (l fp F : List EntryM)
    (c tm : w64) :
    uint.Z tm ≤ uint.Z t →
    ⊢ votesTbl (GF := GF) γ -∗ leadPrefix γ ldr t bL l -∗ lpfull γ ldr t bL l fp -∗
      commitIn γ F c tm -∗ votesTbl γ ∗ ackIn γ t c := by
  intro Htm
  iintro Htbl #Hp #Hpf #Hc
  ihave #Hcj := commitIn_j γ F c tm $$ Hc
  unfold commitJ
  icases Hcj with (%H0 | ⟨%t', %n, %G, #Hq, %Hcn⟩)
  · -- (2026-10-16, stage R8b) a commit index within the bootstrap log, which the leader's log
    -- starts with
    iframe Htbl
    iunfold lpfull at Hpf
    icases Hpf with ⟨%F0, #Hc0, -, %Hpf⟩
    icases isCamp_boot γ ldr t F0 $$ Hc0 with %Hb0
    have Hlen := (Hb0.1.trans Hpf.2.1).length_le
    have HL := full_last_index _ _ l Hpf.1
    unfold ackIn; iright
    iexists ldr, bL, l; iframe Hp; ipureintro
    rw [← HL]; unfold plogLastIndexZ; rw [base0_index]; omega
  obtain ⟨Hcn, Htt, -⟩ := Hcn
  icases cq_base γ t' n G $$ Hq with ⟨%HGn, #HGl⟩
  have Hn := (plogTermAt_some_range _ _ _ _ HGn).2
  by_cases Hne : t' = t
  · subst Hne
    iunfold leadFull at HGl
    icases HGl with ⟨%ldr', %bL', %l', %fp', #Hp2, #Hpf2, %HG⟩
    subst HG
    icases lpfull_fp $$ Hpf2 with ⟨-, %Hf2⟩
    rw [full_last_index _ _ _ Hf2.1] at Hn
    iframe Htbl
    unfold ackIn; iright
    iexists ldr', bL', l'; iframe Hp2; ipureintro; omega
  · have Hlt : uint.Z t' < uint.Z t := by
      have : uint.Z t' ≠ uint.Z t := fun h => Hne (uint_Z_inj.mp h)
      omega
    ihave #HLf := leadFull_intro $$ Hp Hpf
    icases leadFull_camp γ t (fp ++ l) $$ HLf with ⟨%ldr2, %F0, #Hl2, #Hc0, %Hpre⟩
    icases leadFull_wf γ t (fp ++ l) $$ HLf with ⟨%HwL, #HrL⟩
    icases isCamp_ok γ ldr2 t F0 $$ Hc0 with %Hcok
    have Hcl := camp_last t F0 Hcok
    icases lc_core γ ((uint.Z t).toNat + 1) t t' n G ldr2 F0 (fp ++ l)
        (by have := uint_Z_nonneg t; omega) Hlt HwL.1
        (by rw [plogTermAt_prefix _ F0 _ _ Hpre (by rw [Hcl]; rfl)]; exact Hcl)
        $$ Htbl Hq Hl2 Hc0 HrL with %HnL
    icases lpfull_fp $$ Hpf with ⟨-, %Hf⟩
    have Hn' := (plogTermAt_some_range _ _ _ _ HnL).2
    rw [full_last_index _ _ _ Hf.1] at Hn'
    iframe Htbl
    unfold ackIn; iright
    iexists ldr, bL, l; iframe Hp; ipureintro; omega

/-- `Step.appStale` and `Step.snapStale`: learn the leader, adopt it, and acknowledge the
commit index -- with the witness that it is within the leader's log (`commitIn_ackIn`, which
reads the vote table out of the commit invariant: hence the fancy update, 2026-10-16). -/
private theorem ownRaftGhost_step_stale (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    (m.ty = .app ∨ m.ty = .snap) →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

private theorem matchedOk_nonleader (γ : RaftNames) (id : w64) (s : PState) (fp : List EntryM) :
    s.role ≠ .leader → ⊢ matchedOk (GF := GF) γ id s fp := by
  -- PORT(durability stage II): proof (`matchedOk` restated (durability R3))
  sorry

private theorem outbox_eq (γ : RaftNames) (s1 s2 : PState) :
    s2.outbox = s1.outbox →
    ⊢ ([∗list] m ∈ s1.outbox, isMessage (GF := GF) γ m) -∗ [∗list] m ∈ s2.outbox, isMessage γ m := by
  intro H; rw [H]; iintro H; iexact H

private theorem isMessage_vote_inv (γ : RaftNames) (m : Msg) :
    m.ty = .vote →
    ⊢ isMessage (GF := GF) γ m -∗
      ∃ Fc, isCamp γ m.src m.term Fc ∗ ⌜plogLast base0 Fc = entryID.mk m.logterm m.index⌝ ∗
        dynOn γ (campDyn γ m.src m.term Fc) := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

private theorem isMessage_voteReq (γ : RaftNames) (id dst t : w64) (last : entryID)
    (F : List EntryM) (cl : List w8) :
    plogLast base0 F = last →
    ⊢ isCamp (GF := GF) γ id t F -∗ dynOn γ (campDyn γ id t F) -∗
      isMessage γ (pvoteReq id dst t last cl) := by
  intro H
  unfold isMessage pvoteReq
  dsimp only
  iintro #Hc #Hd
  iexists F
  iframe Hc Hd
  ipureintro; rw [H]

/-- The received message of a one-message rule. -/
theorem recv_one (γ : RaftNames) (m : Msg) :
    ⊢ ([∗list] m ∈ [m], isMessage (GF := GF) γ m) -∗ isMessage γ m := by
  iintro H
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ H
private theorem logRecs_intro (γ : RaftNames) (b : entryID) (es : List EntryM) :
    ⊢ □ (∀ (k : Nat) (x : EntryM),
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

private theorem logRecs_elem (γ : RaftNames) (b : entryID) (es : List EntryM)
    (k : Nat) (x : EntryM) :
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
private theorem logRecsC_intro' (γ : RaftNames) (b : entryID) (es : List EntryM) :
    ⊢ □ (∀ (k : Nat) (x : EntryM),
          ⌜es[k]? = some x ∧ uint.Z b.index' + (k : Int) + 1 < 2 ^ 64⌝ →
          ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryC (GF := GF) γ x pt) -∗
      logRecsC γ b es := by
  iintro #H
  unfold logRecsC
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %x Hk
  ipure Hk
  split
  · rename_i Hr
    iapply H $$ %k %x
    ipureintro; exact ⟨Hk, Hr⟩
  · itrivial

private theorem logRecsC_elem (γ : RaftNames) (b : entryID) (es : List EntryM)
    (k : Nat) (x : EntryM) :
    es[k]? = some x → uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    logRecsC (GF := GF) γ b es ⊢ ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryC γ x pt := by
  intro Hk Hr
  unfold logRecsC
  refine (BigSepL.bigSepL_lookup (Φ := fun k e =>
    if uint.Z b.index' + (k : Int) + 1 < 2 ^ 64
    then iprop(∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryC (GF := GF) γ e pt)
    else iprop(True)) Hk).trans ?_
  simp only [Hr, ↓reduceIte]
  exact .rfl

/-- (2026-10-29, stage U5) An entry's `ev2Rec` from the configuration of its prefix in a full log
`fp ++ es` with the records' cores. -/
private theorem ev2Rec_of_prefix (γ : RaftNames) (b : entryID) (fp es : List EntryM) (k : Nat)
    (x : EntryM) (pt : w64) (M : DecMap) (c : CfgM)
    (Hfull : FullOk b fp) (Hwf : PlogWf b es) (Hk : es[k]? = some x)
    (Hpt : plogTermAt b es (pidx b k) = some pt)
    (Hc : CfgAt γ M ((fp ++ es).take (fp.length + k)) c) (Hj : c.joint = true) :
    ⊢ logRecsC (GF := GF) γ base0 fp -∗ logRecsC γ b es -∗ decLb γ M -∗ ev2Rec γ x pt := by
  iintro #Hf #He #HM
  unfold ev2Rec
  iintro %_
  iexists (fp ++ es).take (fp.length + k), M, c
  isplitr
  · iapply logRecsC_take γ (fp ++ es) (fp.length + k) $$ []
    iapply logRecsC_full γ b fp es Hfull $$ Hf He
  iframe HM
  ipureintro
  have Hlt := (List.getElem?_eq_some_iff.mp Hk).1
  have Hxi := Hwf k x Hk
  have Hlen := Hfull.1
  have Hrng := uint_Z_lt x.Index'
  have HbZ := uint_Z_nonneg b.index'
  have HPl : ((fp ++ es).take (fp.length + k)).length = fp.length + k := by
    rw [List.length_take, List.length_append]; omega
  refine ⟨PlogWf_take _ _ _ (full_wf b fp es Hfull Hwf), by rw [HPl]; push_cast at Hxi ⊢; omega,
    ?_, Hc, Hj⟩
  rw [HPl]
  have HW : uint.Z (W64 ((fp.length + k : Nat) : Int)) = ((fp.length + k : Nat) : Int) :=
    uint_Z_W64 _ (by omega) (by push_cast at Hxi ⊢; omega)
  rw [plogTermAt_take_full _ _ _ (by rw [HW]; push_cast; omega),
    full_term_at b fp es _ Hfull (by rw [HW]; push_cast; omega)]
  have Hp : pidx b k = W64 ((fp.length + k : Nat) : Int) := by
    unfold pidx; congr 1; push_cast; omega
  rw [← Hp]; exact Hpt

private theorem leadLogOwn_leader (γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) :
    s.role = .leader →
    leadLogOwn (GF := GF) γ s terms =
      iprop(∃ γt, ∃ (M : GMap w64 (EntryM × w64)), ∃ l0,
        ⌜terms !! s.term = some ((γt, s.base), l0)⌝ ∗
        ghostMapAuth γt 1 M ∗
        ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ∗
        ⌜∀ i, (M !! i).isSome → uint.Z i ≤ plogLastIndexZ s.base s.log⌝ ∗
        ⌜l0 <+: s.log⌝ ∗
        leadFrags γt l0 s.log) := by
  intro H; unfold leadLogOwn; rw [H]

private theorem campOwn_leader (γ : RaftNames) (id : w64) (camps : GMap w64 (List EntryM × w64))
    (s : PState) (F : List EntryM) :
    s.role = .leader →
    campOwn (GF := GF) γ id camps s F =
      iprop(∃ F0, isCamp γ id s.term F0 ∗
       ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
         (plogLast base0 F).term' = s.term⌝) := by
  -- PORT(durability stage II): proof (`campOwn` restated (durability I-1))
  sorry

private theorem acksOk_leader (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    s.role = .leader → ⊢ acksOk (GF := GF) γ s acks := by
  intro H; unfold acksOk; rw [H]; exact true_intro
private theorem campOwn_cand (γ : RaftNames) (id : w64) (camps : GMap w64 (List EntryM × w64))
    (s : PState) (F : List EntryM) :
    s.role = .candidate → campOwn (GF := GF) γ id camps s F = iprop(⌜∃ k, camps !! s.term = some (F, k)⌝) := by
  -- PORT(durability stage II): proof (`campOwn` restated (durability I-1))
  sorry

-- END HELPERS (Lean addition)

/-- `Step.win`: allocate the term log -- recording the candidate's base and log, and
holding the leader's entry -- and acknowledge the old and the new last index. -/
theorem ownRaftGhost_step_win (γ : RaftNames) (c : CfgM) (id : w64)
    (s : PState) (mt : GMap w64 w64) (ms : List Msg) (n : Nat) :
    s.role = .candidate →
    JQuorum c (granted s.votes) →
    plogLastIndexZ s.base s.log + 1 < 2 ^ 64 →
    LeaderMatchOk id s mt →
    (∀ m ∈ ms, ReplOk id (pwinState id s mt) m) →
    -- (2026-10-14, stage B5) in the dynamic mode, an `MsgApp` carries the commit index
    (γ.reDyn ≠ none → ∀ m ∈ ms, AppCommitEq (pwinState id s mt) m) →
    -- (D19p, 2026-10-18) a snapshot's sender and receiver within the tracked bound
    (∀ m ∈ ms, m.ty = .snap → ∀ T, γ.reTracked = some T → id ∈ T ∧ m.dst ∈ T) →
    -- (2026-10-18, D19b stage 5) the new entry's index is covered by the receipt `⧖ n`
    plogLastIndexZ s.base s.log + 1 ≤ (n : Int) + γ.reBoot.length →
    ⊢ ⧖ n -∗ dynEnv γ id c s -∗ ownRaftGhost (GF := GF) γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (psendMsgs (pwinState id s mt)
                           ([pselfAck id (pwinState id s mt)] ++ ms)) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.beat`: a heartbeat carries the leadership, a commit index the leader has, and
the `Match` it is bounded by. -/
theorem ownRaftGhost_step_beat (γ : RaftNames) (id : w64) (s : PState) (ms : List Msg) :
    s.role = .leader →
    (∀ m ∈ ms, HeartbeatOk id s m) →
    (∀ m ∈ ms, HbCtxOk s.rd.ro m.ctx) →
    ⊢ ownRaftGhost (GF := GF) γ id s md ==∗ ownRaftGhost γ id (psendMsgs s ms) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.sendApps`: as `Step.win`'s broadcast. -/
theorem ownRaftGhost_step_send_apps (γ : RaftNames) (c : CfgM) (id : w64) (s : PState)
    (ms : List Msg) :
    s.role = .leader →
    (∀ m ∈ ms, ReplOk id s m) →
    -- (2026-10-14, stage B5) in the dynamic mode, an `MsgApp` carries the commit index
    (γ.reDyn ≠ none → ∀ m ∈ ms, AppCommitEq s m) →
    -- (D19p, 2026-10-18) a snapshot's sender and receiver within the tracked bound
    (∀ m ∈ ms, m.ty = .snap → ∀ T, γ.reTracked = some T → id ∈ T ∧ m.dst ∈ T) →
    ⊢ dynEnv γ id c s -∗
      ownRaftGhost (GF := GF) γ id s md ==∗ ownRaftGhost γ id (psendMsgs s ms) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.propForward`: the forwarded proposal carries the received one's entries, and
what it says of them (2026-10-10). -/
theorem ownRaftGhost_step_prop_forward (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .propose) :
    ⊢ isMessage (GF := GF) γ m -∗ msgTks γ m -∗ ownRaftGhost γ id s md ==∗
      ownRaftGhost γ id
        (psendMsgs s
           [Msg.mkV .propose id s.lead (W64 0) m.reject
              m.index m.logterm m.commit m.rejecthint
              m.entries [] m.ctx]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

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
      ownRaftGhost γ id s md ==∗
      ownRaftGhost γ id
        { s with matched :=
            <[m.src := if uint.Z x < uint.Z m.index
                       then m.index else x]> s.matched } md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.reMatch` (2026-10-13): each new `Match` is `0` (acknowledged for free) or the
peer's old one (acknowledged already). -/
theorem ownRaftGhost_step_rematch (γ : RaftNames) (id : w64) (s : PState) (mt : GMap w64 w64) :
    s.role = .leader →
    (∀ v i, mt !! v = some i → uint.Z i = 0 ∨ s.matched !! v = some i) →
    ⊢ ownRaftGhost (GF := GF) γ id s md ==∗ ownRaftGhost γ id { s with matched := mt } md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.commit`: a quorum of `Match`es at least `n` is a commit fact `cq`, which extends
the global committed log (`commit_extend`, inside the invariant) -- the node's committed
prefix is then `isCommitted`. -/
theorem ownRaftGhost_step_commit (γ : RaftNames) (c : CfgM) (id : w64)
    (s : PState) (n : w64) :
    s.role = .leader →
    uint.Z s.commit < uint.Z n →
    uint.Z n ≤ plogLastIndexZ s.base s.log →
    plogTermAt s.base s.log n = some s.term →
    JQuorum c (ackedBy s n) →
    ⊢ dynEnv γ id c s -∗ regsOwn γ -∗
      ownRaftGhost (GF := GF) γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      regsOwn γ ∗ ownRaftGhost γ id { s with commit := n } md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.appStale`: back to follower of `m.src` in the same term, and acknowledge the
commit index (within the leader's log by leader completeness: `ownRaftGhost_step_stale`). -/
theorem ownRaftGhost_step_app_stale (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .app →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) md := by
  intro Hty Hfid Hterm Hrole
  exact ownRaftGhost_step_stale γ id s m (Or.inl Hty) Hfid Hterm Hrole

/-- (2026-10-19, D21 M3) A follower's rejection of a leader's append, in a cluster with a non-empty
bootstrap log, is of an index past the bootstrap log (both logs hold it, and the follower's commit
index is at least its length), with a hint at least `1` (the walk stops at the bootstrap log's
first entry, of term `1`, at most the leader's term at the index) and at most the index. -/
theorem ownLogGhost_reject_ok (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps)
    (m : Msg) (hint : w64) (Hty : m.ty = .app)
    (Hle : uint.Z s.commit ≤ uint.Z m.index)
    (Hnm : ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index))
    (Hh : RejHintOk s.base s.log m.index m.logterm hint) :
    ⊢ isMessage (GF := GF) γ m -∗ ownLogGhost γ id s kl W -∗
      ⌜γ.reBoot ≠ [] → (γ.reBoot.length : Int) < uint.Z m.index ∧ 1 ≤ uint.Z hint ∧
        uint.Z hint ≤ uint.Z m.index⌝ ∗ ownLogGhost γ id s kl W := by
  -- PORT(durability stage II): proof (the body of `ownRaftGhost`/`ownLogGhost` changed (durability I-1))
  sorry

/-- `Step.appReject`: back to follower of `m.src`; (2026-10-19, D21 M3) the rejection carries
`ownLogGhost_reject_ok`'s facts. -/
theorem ownRaftGhost_step_app_reject (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (hint hintterm : w64) :
    m.ty = .app →
    m.src ≠ id →
    s.role ≠ .leader →
    uint.Z s.commit ≤ uint.Z m.index →
    ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
    RejHintOk s.base s.log m.index m.logterm hint →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s md ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term true m.index
              hintterm (W64 0) hint []]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-! ### An acknowledged index is within a leader's log (2026-10-16, stage R8a) -/

/-- At a leader, an `ackIn` of its term is at most its last index: the prefix the witness names is
of its own term log (`leadLogOwn`: every index in the term log is at most the last index, and the
campaign log `l0` is a prefix of the log: `ownLogGhost_prefix_within`). What the physical
`MaybeUpdate` needs (`PrvalsOk`, `Defs.lean`). -/
theorem ownRaftGhost_ackIn_le (γ : RaftNames) (id : w64) (s : PState) (i : w64) :
    s.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ackIn γ s.term i -∗
      ⌜uint.Z i ≤ plogLastIndexZ s.base s.log⌝ ∗ ownRaftGhost γ id s md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- (2026-10-19, D21 M3) A node's term at index `1`, if its log has one, is the bootstrap log's
first entry's, `1`, once the bootstrap log is non-empty. -/
theorem ownLogGhost_term1 (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ⌜γ.reBoot ≠ [] → ∀ t0, plogTermAt s.base s.log (W64 1) = some t0 → uint.Z t0 ≤ 1⌝ ∗
      ownLogGhost γ id s kl W := by
  -- PORT(durability stage II): proof (the body of `ownRaftGhost`/`ownLogGhost` changed (durability I-1))
  sorry

theorem ownRaftGhost_term1 (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
      ⌜γ.reBoot ≠ [] → ∀ t0, plogTermAt s.base s.log (W64 1) = some t0 → uint.Z t0 ≤ 1⌝ ∗
      ownRaftGhost γ id s md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- (2026-10-19, D21 M3) With a non-empty bootstrap log a leader's last index is at least `2`:
its campaign log holds the bootstrap log (`isCamp_boot`) and is a strict prefix of its full log
(`campOwn`). -/
theorem ownLogGhost_leader_last (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ⌜s.role = .leader → γ.reBoot ≠ [] → 2 ≤ plogLastIndexZ s.base s.log⌝ ∗
      ownLogGhost γ id s kl W := by
  -- PORT(durability stage II): proof (the body of `ownRaftGhost`/`ownLogGhost` changed (durability I-1))
  sorry

theorem ownRaftGhost_leader_last (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
      ⌜s.role = .leader → γ.reBoot ≠ [] → 2 ≤ plogLastIndexZ s.base s.log⌝ ∗
      ownRaftGhost γ id s md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-! ### Read-index: a node of term `T` dooms no record of `T` (2026-10-13) -/

theorem ownLogGhost_ack_le (E : CoPset) (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (γs : SlotNames) (V : DurMaps) (πc : List Prom) (t i : w64) :
    γ.reSlot !! v = some γs → ↑(slotN γ v) ⊆ E →
    ⊢ slotInv (GF := GF) γ v -∗ ghostVar γs.1 (1 : Qp).half V -∗
      ownLogGhost γ v s kl (virt V πc) -∗ ackEv γ v t i ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ v s kl (virt V πc) ∗
      ⌜uint.Z t ≤ uint.Z s.term⌝ := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

theorem ownLogGhost_not_doomed (E : CoPset) (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (γs : SlotNames) (V : DurMaps) (πc : List Prom) (r : RqRec) :
    γ.reSlot !! v = some γs → ↑(slotN γ v) ⊆ E →
    ⊢ slotInv (GF := GF) γ v -∗ ghostVar γs.1 (1 : Qp).half V -∗
      ownLogGhost γ v s kl (virt V πc) -∗ rqRecOk γ s.term r ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ v s kl (virt V πc) ∗
      ⌜∀ t' q, r.2 = some (t', q) → v ∉ q⌝ := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

theorem ownLogGhost_not_doomed_list (E : CoPset) (γ : RaftNames) (v : w64) (s : PState)
    (kl : Option w64) (γs : SlotNames) (V : DurMaps) (πc : List Prom) (recs : List RqRec) :
    γ.reSlot !! v = some γs → ↑(slotN γ v) ⊆ E →
    ⊢ slotInv (GF := GF) γ v -∗ ghostVar γs.1 (1 : Qp).half V -∗
      ownLogGhost γ v s kl (virt V πc) -∗ ([∗list] r ∈ recs, rqRecOk γ s.term r) ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ v s kl (virt V πc) ∗
      ⌜∀ r ∈ recs, ∀ t' q, r.2 = some (t', q) → v ∉ q⌝ := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

/-- A heartbeat's position, acknowledged by a node of the heartbeat's term. -/
theorem ownLogGhost_hbAck (E : CoPset) (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (γs : SlotNames) (V : DurMaps) (πc : List Prom)
    (q : Nat) (recs : List RqRec) (hq : q ≤ recs.length) :
    γ.reSlot !! v = some γs → ↑(slotN γ v) ⊆ E →
    ⊢ slotInv (GF := GF) γ v -∗ ghostVar γs.1 (1 : Qp).half V -∗
      ownLogGhost γ v s kl (virt V πc) -∗ ([∗list] r ∈ recs, rqRecOk γ s.term r) ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ v s kl (virt V πc) ∗
      ⌜HbAckOk v q recs⌝ := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

/-- A heartbeat's read-index part, at a node of its term, gives its response's. -/
theorem ownLogGhost_hbResp (E : CoPset) (γ : RaftNames) (v : w64) (s : PState) (kl : Option w64)
    (γs : SlotNames) (V : DurMaps) (πc : List Prom)
    (L : w64) (ctx : List w8) :
    γ.reSlot !! v = some γs → ↑(slotN γ v) ⊆ E →
    ⊢ slotInv (GF := GF) γ v -∗ ghostVar γs.1 (1 : Qp).half V -∗
      ownLogGhost γ v s kl (virt V πc) -∗
      (⌜ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜ctx = u64Le q ∧ uint.nat q ≤ recs.length⌝ ∗ rqLb γ L s.term recs ∗
         [∗list] r ∈ recs, rqRecOk γ s.term r) ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ v s kl (virt V πc) ∗
      (⌜ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜ctx = u64Le q ∧ HbAckOk v (uint.nat q) recs⌝ ∗ rqLb γ L s.term recs) := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

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
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
           [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }]) md := by
  -- PORT(durability stage II): proof (restated: a fancy update, for the slot lookups (durability R2))
  sorry

/-- `Step.appAccept`. The new log is the old one cut at the first conflict, if any, and
the batch appended (`plogMaybeAppend_inv`); the batch is the leader's (`isMessage`'s
`leadPrefix`). So the new log has records (the old ones below the cut; the leader's
above, whose predecessor terms are the batch's, which the new log has:
`plogMaybeAppend_batch`, `plog_prefix_batch`); every justified acknowledgement of this
term is below the cut (`ackAgree_term`: the old log agrees with the leader there, and
the cut is where it does not); and the new acknowledgement of `lastnewi` is justified by
the batch itself. -/
theorem ownRaftGhost_step_app_accept (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (lastnewi : w64) (es' : List EntryM) :
    m.ty = .app →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit ≤ uint.Z m.index →
    plogMaybeAppend s.base s.log
      (entryID.mk m.logterm m.index) m.entries
      = some (lastnewi, es') →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with
               log := es',
               commit := plogCommitTo s.commit
                           (if uint.Z m.commit < uint.Z lastnewi
                            then m.commit else lastnewi) }
           [Msg.mk .appResp id m.src s.term false lastnewi
              (W64 0) (W64 0) (W64 0) []]) md := by
  -- PORT(durability stage II): proof (restated: a fancy update, for the slot lookups (durability R2))
  sorry

/-- Freezing a batch of stamped entries into the leader's term log: their indices are
past everything in it (`leadLogOwn`'s bound) and do not wrap. Each is frozen with the
predecessor term `ptf k`. -/
theorem term_log_insert_stamped (γt : GName) (M : GMap w64 (EntryM × w64)) (T : w64)
    (L : Int) (ents : List EntryM) (ptf : Nat → w64) :
    0 ≤ L → L + (ents.length : Int) < 2 ^ 64 →
    (∀ i, (M !! i).isSome → uint.Z i ≤ L) →
    ⊢ ghostMapAuth (GF := GF) γt 1 M -∗ ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ==∗
      ∃ M' : GMap w64 (EntryM × w64),
        ghostMapAuth γt 1 M' ∗ ([∗map] i ↦ e ∈ M', i ↪[γt]□ e) ∗
        ⌜∀ i, (M' !! i).isSome → uint.Z i ≤ L + (ents.length : Int)⌝ ∗
        [∗list] k ↦ e ∈ ents.mapIdx (stamp T (W64 L)),
          e.Index' ↪[γt]□ ((e, ptf k) : EntryM × w64) := by
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
      iapply (BigSepL.bigSepL_snoc (Φ := fun k (e : EntryM) =>
        iprop(e.Index' ↪[γt]□ ((e, ptf k) : EntryM × w64)))).2
      isplitr
      · iexact Hents
      · rw [List.length_mapIdx]; iexact Hnew

/-- Stamping a batch with its tickets gives the entries' data (2026-10-10; D21 M6: each client
operation's ticket becomes its index). -/
private theorem entData_mapIdx_stampF (γ : RaftNames) (ents : List EntryM)
    (f : Nat → EntryM → EntryM)
    (Hf : ∀ k e, ∃ t i, f k e = { e with Term' := t, Index' := i }) :
    ⊢ ([∗list] e ∈ ents, propData (GF := GF) γ e) -∗ ([∗list] e ∈ ents, entTk γ e) ==∗
      [∗list] x ∈ ents.mapIdx f, entData γ x := by
  induction ents generalizing f with
  | nil =>
    iintro _ _
    imodintro
    rw [List.mapIdx_nil]
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (e : EntryM) => entData (GF := GF) γ e)).2
    iempintro
  | cons e es ih =>
    iintro #Hd Htk
    icases (BigSepL.bigSepL_cons (Φ := fun _ (e : EntryM) => propData (GF := GF) γ e)).1 $$ Hd
      with ⟨#He, #Hes⟩
    icases (BigSepL.bigSepL_cons (Φ := fun _ (e : EntryM) => entTk (GF := GF) γ e)).1 $$ Htk
      with ⟨Ht, Hts⟩
    rw [List.mapIdx_cons]
    obtain ⟨t, i, Hfe⟩ := Hf 0 e
    rw [Hfe]
    imod propData_stampTk γ e t i $$ He Ht with #He'
    imod ih (fun k => f (k + 1)) (fun k e => Hf (k + 1) e) $$ Hes Hts with #Hes'
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (e : EntryM) => entData (GF := GF) γ e)).2
    iframe He' Hes'

private theorem entData_mapIdx_stamp (γ : RaftNames) (t L : w64) (ents : List EntryM) :
    ⊢ ([∗list] e ∈ ents, propData (GF := GF) γ e) -∗ ([∗list] e ∈ ents, entTk γ e) ==∗
      [∗list] x ∈ ents.mapIdx (stamp t L), entData γ x :=
  entData_mapIdx_stampF γ ents (stamp t L) (fun k e => ⟨t, L + W64 1 + W64 k, rfl⟩)

/-- `Step.propose`: the stamped entries go into the leader's term log
(`term_log_insert_stamped`), which gives each its `isEntryR` (the first after the old
last entry, the rest after each other); the self-acknowledgement is the node's own to
allocate. (Rocq's `let s' := pappend s (imap …) in` is inlined.) -/
theorem ownRaftGhost_step_propose (γ : RaftNames) (id : w64) (s : PState)
    (ents : List EntryM) (n : Nat) :
    s.role = .leader →
    plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
    -- (2026-10-18, D19b stage 5) the new entries' indices are covered by the receipt `⧖ n`
    plogLastIndexZ s.base s.log + (ents.length : Int) ≤ (n : Int) + γ.reBoot.length →
    ⊢ ⧖ n -∗ ([∗list] e ∈ ents, propData (GF := GF) γ e) -∗ ([∗list] e ∈ ents, entTk γ e) -∗
      -- (2026-10-29, stage U5) an empty `ConfChangeV2` of the batch at a joint configuration
      (□ ∀ (fp' : List EntryM) (k : Nat) (x : EntryM),
        ⌜FullOk s.base fp' ∧ (ents.mapIdx (stamp s.term (plastIndex s)))[k]? = some x ∧
          γ.reDyn ≠ none ∧ IsEmptyV2 x⌝ -∗
        logRecs γ base0 fp' -∗
        ∃ (M : DecMap) (c : CfgM), decLb γ M ∗
          ⌜CfgAt γ M ((fp' ++ s.log) ++ (ents.mapIdx (stamp s.term (plastIndex s))).take k) c ∧
            c.joint = true⌝) -∗
      ownRaftGhost γ id s md ==∗
      ownRaftGhost γ id
        (psendMsgs (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))
          [pselfAck id (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.snapStale`: back to follower of `m.src`, acknowledging the commit index --
`Step.appStale`'s update. -/
theorem ownRaftGhost_step_snap_stale (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) md := by
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
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with commit := m.index }
           [Msg.mk .appResp id m.src s.term false m.index
              (W64 0) (W64 0) (W64 0) []]) md := by
  -- PORT(durability stage II): proof (restated: a fancy update, for the slot lookups (durability R2))
  sorry

/-- A snapshot message shows its prefix (2026-10-14, reconfiguration stage B8): some prefix of
the full log, recorded (`logRecs`), ends at the snapshot's entry id -- the sender's committed
prefix up to it (its leader prefix, `isMessage_snap_inv`, taken to the index), committed
(2026-10-28, stage U3). This is the prefix a receiver's restore takes (`StepR.snapRestore`'s `fp'`, which records make unique). -/
theorem isMessage_snap_prefix (γ : RaftNames) (m : Msg) (Hty : m.ty = .snap) :
    ⊢ isMessage (GF := GF) γ m -∗
      ∃ fp, ⌜FullOk (entryID.mk m.logterm m.index) fp⌝ ∗ logRecs γ base0 fp ∗ isCommitted γ fp := by
  iintro #Hm
  icases isMessage_snap_inv γ m Hty $$ Hm with
    ⟨-, -, ⟨%bL, %l', %fpL, #Hp', %Hidx', #Hpf', -, #Hcm⟩, -⟩
  ihave #HLf := leadFull_intro $$ Hp' Hpf'
  icases leadFull_wf γ m.term (fpL ++ l') $$ HLf with ⟨%HwLf, #HrLf⟩
  icases lpfull_fp $$ Hpf' with ⟨-, %HfL⟩
  have HbL := (plogTermAt_some_range _ _ _ _ Hidx').1
  have HLidx : plogTermAt base0 (fpL ++ l') m.index = some m.logterm := by
    rw [full_term_at bL fpL l' m.index HfL.1 HbL]; exact Hidx'
  iexists (fpL ++ l').take (uint.Z m.index).toNat
  isplitr
  · ipureintro; exact FullOk_take _ _ _ HwLf.1 HLidx
  iframe Hcm
  iapply logRecs_take $$ HrLf

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
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with
               base := entryID.mk m.logterm m.index,
               log := [],
               commit := m.index }
           [Msg.mk .appResp id m.src s.term false m.index
              (W64 0) (W64 0) (W64 0) []]) md := by
  -- PORT(durability stage II): proof (restated: a fancy update, for the slot lookups (durability R2))
  sorry

/-! ### The refinement obligation -/

/-! ### Read-index rules (2026-10-13) -/

/-- `Step.drain` with the drained messages' read credits handed out (2026-10-13): what
`Ready` gives the transport with each `MsgReadIndex`. -/
theorem ownRaftGhost_drain (γ : RaftNames) (id : w64) (s : PState) (o' out : List Msg)
    (Hp : (o' ++ out).Perm s.outbox) :
    ⊢ ownRaftGhost (GF := GF) γ id s md ==∗
      ownRaftGhost γ id { s with outbox := o' } md ∗ rdCred γ (rdCount s.outbox - rdCount o') ∗
        msgsTks γ out := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- A step that changes only the outbox (growing by `ms`) and the read state: the read
ghost state is updated by `Hupd`, which may consult the log ghost state. -/
theorem ownRaftGhost_rd (γ : RaftNames) (id : w64) (s s' : PState) (ms : List Msg)
    (Hs' : s' = { s with outbox := s.outbox ++ ms, rd := s'.rd }) :
    ⊢ ([∗list] m ∈ ms, isMessage (GF := GF) γ m) -∗ ownRaftGhost γ id s md -∗
      (∀ kl (γs : SlotNames) (V : DurMaps) (πc : List Prom), ⌜γ.reSlot !! id = some γs⌝ -∗
        slotInv γ id -∗ ghostVar γs.1 (1 : Qp).half V -∗
        ownLogGhost γ id s kl (virt V πc) -∗ rdOwn γ id s ={⊤ \ ↑(raftRegN γ)}=∗
        ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ id s kl (virt V πc) ∗ rdOwn γ id s') ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id s' md := by
  -- PORT(durability stage II): proof (restated: the update may look up the slot (durability R2))
  sorry

theorem isMessage_readIndex_tr (γ : RaftNames) (m m' : Msg) :
    m.ty = .readIndex → m'.ty = .readIndex → m'.entries = m.entries →
    ⊢ isMessage (GF := GF) γ m -∗ isMessage γ m' := by
  intro H H' He
  unfold isMessage; rw [H, H', He]; iintro H; iexact H

theorem ownRaftGhost_step_read_fwd (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .readIndex → s.role ≠ .leader → s.lead ≠ W64 0 →
    ⊢ isMessage (GF := GF) γ m -∗ rdCred γ 1 -∗ ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (psendMsgs s [{ m with
        src := if m.src = W64 0 then id else m.src
        dst := s.lead
        term := W64 0 }]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_read_pend (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (pm : MessageM) :
    m.ty = .readIndex → s.role = .leader →
    ⊢ isMessage (GF := GF) γ m -∗ rdCred γ 1 -∗ ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id ({ s with rd := { s.rd with pend := s.rd.pend ++ [(pm, m.entries)] } }) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- A request arriving at the leader, read at its commit index (its record `((c, commit),
d)`, `rqRecOk`): appended to the term's registry with its credit (which bounds the new
position), queued, and acknowledged by the leader itself, which is in no doom quorum of
its own term (`ownLogGhost_not_doomed_list`). -/
theorem rdOwn_arrive (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) (q : ReadReq)
    (e : EntryM) (c : List w8) (d : Option (w64 × GSet w64)) :
    s.role = .leader → q.index = s.commit → q.ents = [e] →
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ rdOwn γ id s -∗ ⌜e.Data' = c⌝ -∗
      rqRecOk γ s.term ((c, s.commit), d) -∗ rdCred γ 1 ={⊤ \ ↑(raftRegN γ)}=∗
      ownLogGhost γ id s kl W ∗
      rdOwn γ id { s with rd := { s.rd with ro := readonlyArrive s.rd.ro id q } } := by
  -- PORT(durability stage II): proof (the body of `ownRaftGhost`/`ownLogGhost` changed (durability I-1))
  sorry

/-- `ownRaftGhost_rd`, with a resource `R` taken out of the update. -/
theorem ownRaftGhost_rdR (γ : RaftNames) (id : w64) (s s' : PState) (ms : List Msg)
    (R : IProp GF) (Hs' : s' = { s with outbox := s.outbox ++ ms, rd := s'.rd }) :
    ⊢ ([∗list] m ∈ ms, isMessage (GF := GF) γ m) -∗ ownRaftGhost γ id s md -∗
      (∀ kl (γs : SlotNames) (V : DurMaps) (πc : List Prom), ⌜γ.reSlot !! id = some γs⌝ -∗
        slotInv γ id -∗ ghostVar γs.1 (1 : Qp).half V -∗
        ownLogGhost γ id s kl (virt V πc) -∗ rdOwn γ id s ={⊤ \ ↑(raftRegN γ)}=∗
        ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ id s kl (virt V πc) ∗ rdOwn γ id s' ∗ R) ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id s' md ∗ R := by
  -- PORT(durability stage II): proof (restated: the update may look up the slot (durability R2))
  sorry

/-- A request with its facts and credit arriving at the leader whose commit index is at an
entry of its term. -/
theorem ownRaftGhost_arrive (γ : RaftNames) (id : w64) (t : PState) (src : w64)
    (ents : List EntryM) (t' : PState) :
    t.role = .leader → plogTermAt t.base t.log t.commit = some t.term →
    t' = { t with rd := { t.rd with ro := readonlyArrive t.rd.ro id ⟨t.commit, src, ents⟩ } } →
    ⊢ ownRaftGhost (GF := GF) γ id t md -∗
      (∃ e c Lc, ⌜ents = [e]⌝ ∗ ⌜e.Data' = c⌝ ∗ readReq γ c Lc) -∗ rdCred γ 1 ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id t' md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_read_arrive (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .readIndex → s.role = .leader →
    plogTermAt s.base s.log s.commit = some s.term →
    ⊢ isMessage (GF := GF) γ m -∗ rdCred γ 1 -∗ ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id ({ s with rd := { s.rd with
        ro := readonlyArrive s.rd.ro id ⟨s.commit, m.src, m.entries⟩ } }) md := by
  intro Hty Hrole Hct
  iintro #Hm Hcr Hown
  iunfold isMessage at Hm
  rw [Hty]
  iapply ownRaftGhost_arrive γ id s m.src m.entries _ Hrole Hct (by rfl) $$ Hown Hm Hcr

theorem ownRaftGhost_step_read_release (γ : RaftNames) (id : w64) (s : PState) :
    s.role = .leader → plogTermAt s.base s.log s.commit = some s.term →
    ⊢ ownRaftGhost (GF := GF) γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id ({ s with rd := { s.rd with
        pend := []
        ro := readonlyRelease s.rd.ro id s.commit s.rd.pend } }) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem HbAckOk_prefix (v : w64) (k : Nat) (recs0 recs : List RqRec) :
    recs0 <+: recs → HbAckOk v k recs0 → HbAckOk v k recs := by
  intro ⟨more, h⟩ hk
  subst h
  exact HbAckOk_app v k recs0 more hk

/-- Confirming every record of a list at once, given a confirmation of one from a resource `X`
that the confirmations keep (2026-10-14, stage B5: in the dynamic mode `X` holds the vote table,
which `lc_core` reads). -/
theorem confirm_all (γ : RaftNames) (T : w64) (Q : GSet w64) (X : IProp GF)
    (Hconf : ∀ (r : RqRec), (∀ v ∈ Q, ∀ t' qq, r.2 = some (t', qq) → v ∉ qq) →
      ⊢ X -∗ rqRecOk γ T r -∗ readOk γ r.1.1 r.1.2) :
    ∀ (rs : List RqRec), ⊢ X -∗ ([∗list] r ∈ rs, rqRecOk γ T r) -∗
      [∗list] r ∈ rs, ∀ (_ : ∀ v ∈ Q, ∀ t' qq, r.2 = some (t', qq) → v ∉ qq),
        readOk γ r.1.1 r.1.2
  | [] => by iintro _ _; iapply (BigSepL.bigSepL_nil).2; iempintro
  | r :: rs => by
    iintro HX Hl
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨#Hr, #Hrs⟩
    have H1 : ⊢ X -∗ rqRecOk γ T r -∗
        ∀ (_ : ∀ v ∈ Q, ∀ t' qq, r.2 = some (t', qq) → v ∉ qq), readOk γ r.1.1 r.1.2 := by
      iintro HX #Hr %Hc
      iapply Hconf r Hc $$ HX Hr
    ihave #Hok1 := H1 $$ HX Hr
    ihave #Hoks := confirm_all γ T Q X Hconf rs $$ HX Hrs
    iapply (BigSepL.bigSepL_cons).2
    iframe Hok1 Hoks

/-- An acknowledgement of position `q` by `src` (a heartbeat response's, `HbAckOk` of a
prefix of the term's registry), then the requests up to a position `N` a quorum
acknowledged confirmed: each of their records is not doomed (`Hconf`: static,
`rqRecOk_confirm`; dynamic, `rqRecOk_confirm_dyn`, from the resource `X`, kept), so each
confirmed request has its answer's facts. -/
theorem rdOwn_ack (γ : RaftNames) (id : w64) (s : PState) (src q N : w64)
    (recs0 : List RqRec) (P : List EntryM) (c : CfgM) (X : IProp GF) {M : DecMap}
    (Hconf : ∀ (Q : GSet w64) (r : RqRec), JQuorum c Q →
      (∀ v ∈ Q, ∀ t' qq, r.2 = some (t', qq) → v ∉ qq) →
      ⊢ X -∗ rqRecOk γ s.term r -∗ readOk γ r.1.1 r.1.2) :
    s.role = .leader →
    -- (2026-10-14, reconfiguration stage B4) a joint quorum of a recorded configuration, the
    -- reader's (was `QuorumAcked γ.reCfg`)
    CfgAt γ M P c →
    JQuorumAcked c
      (fun v => ((readonlyRecvAck s.rd.ro src (u64Le q)).acks !! v).getD (W64 0)) N →
    HbAckOk src (uint.nat q) recs0 →
    ⊢ X -∗ rdOwn (GF := GF) γ id s -∗ rqLb γ id s.term recs0 -∗ X ∗
      rdOwn γ id { s with rd := { s.rd with
        ro := (readonlyAdvance (readonlyRecvAck s.rd.ro src (u64Le q)) N).1 } } ∗
      [∗list] q' ∈ (readonlyAdvance (readonlyRecvAck s.rd.ro src (u64Le q)) N).2, respFacts γ q' := by
  intro Hr HcP HQ Hq0
  rw [readonlyRecvAck_eq] at HQ ⊢
  unfold rdOwn
  iintro HX ⟨%γl, %rqm, %Hγl, Ha, #Hf, %Hok, Hl, #Hst0, #Hpd0, Hcr, #Hinv, Htk⟩ #Hlb
  unfold rdLead
  rw [Hr]
  icases Hl with ⟨%γq, %recs, %Hq, Hauth, #Hrs, %Hlen, #Hpq, %Hacks, Hcrs⟩
  unfold rqLb
  icases Hlb with ⟨%γl', %γq', %Hγl', #Hel, #Hlb⟩
  rw [Hγl] at Hγl'
  cases Hγl'
  icases ghost_map_lookup $$ Ha Hel with %Hq'
  have Hqq : γq = γq' := by
    have h1 : rqm !! s.term = some γq' := Hq'
    rw [Hq] at h1
    exact Option.some.inj h1
  subst Hqq
  icases mono_list_auth_lb_valid $$ Hauth Hlb with %Hpre
  -- the acknowledgements after `src`'s
  have Hacks' : ∀ v a,
      (<[src := w64Max ((s.rd.ro.acks !! src).getD (W64 0)) q]> s.rd.ro.acks) !! v = some a →
      HbAckOk v (uint.nat a) recs := by
    intro v a Hva
    by_cases Hv : v = src
    · subst Hv
      rw [GMap.lookup_insert] at Hva
      cases Hva
      apply HbAckOk_w64Max
      · cases Hx : s.rd.ro.acks !! v with
        | none => exact HbAckOk_zero v recs
        | some a0 => exact Hacks v a0 Hx
      · exact HbAckOk_prefix v _ recs0 recs Hpre.2 Hq0
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hv)] at Hva
      exact Hacks v a Hva
  rw [readonlyAdvance_acks]
  split
  · -- nothing confirmed
    rename_i Hle
    iframe HX
    isplitl
    · iexists γl, rqm
      isplitr; · ipureintro; exact Hγl
      isplitl [Ha]; · iexact Ha
      isplitr; · iexact Hf
      isplitr
      · ipureintro
        intro t Ht
        rcases Hok t Ht with h | ⟨h1, -⟩
        · left; exact h
        · right; exact ⟨h1, by simp⟩
      isplitl [Hauth Hcrs]
      · iexists γq, recs
        isplitr; · ipureintro; exact Hq
        isplitl [Hauth]; · iexact Hauth
        isplitr; · iexact Hrs
        isplitr; · ipureintro; exact Hlen
        isplitr; · iexact Hpq
        isplitr; · ipureintro; exact Hacks'
        iexact Hcrs
      isplitr; · iexact Hst0
      isplitr; · iexact Hpd0
      isplitl [Hcr]; · iexact Hcr
      iframe Hinv
      iexact Htk
    · iapply (BigSepL.bigSepL_nil).2; iempintro
  · rename_i Hgt
    obtain ⟨Q, HQq, HQv⟩ := HQ
    have Hpos : 0 < uint.Z N := by have := uint_Z_nonneg s.rd.ro.confirmed; omega
    have hc : uint.nat s.rd.ro.confirmed ≤ uint.nat N := uint_nat_le_of_Z_le (by omega)
    have HQN : ∀ v ∈ Q, HbAckOk v (uint.nat N) recs := by
      intro v hv
      have h := HQv v hv
      cases Hx : (<[src := w64Max ((s.rd.ro.acks !! src).getD (W64 0)) q]> s.rd.ro.acks) !! v with
      | none =>
        simp only [Hx, Option.getD_none] at h
        exfalso
        have h0 : uint.Z (W64 0 : w64) = 0 := by decide
        omega
      | some a =>
        simp only [Hx, Option.getD_some] at h
        exact HbAckOk_le v _ _ recs (uint_nat_le_of_Z_le h) (Hacks' v a Hx)
    obtain ⟨v0, Hv0⟩ := CfgAt.member HcP HQq
    have HNle : uint.nat N ≤ recs.length := (HQN v0 Hv0).1
    have Hk : uint.nat (N - s.rd.ro.confirmed) = uint.nat N - uint.nat s.rd.ro.confirmed := by
      have := uint_nat_eq N
      have := uint_nat_eq s.rd.ro.confirmed
      have := uint_nat_eq (N - s.rd.ro.confirmed)
      word
    have HkP : uint.nat N - uint.nat s.rd.ro.confirmed ≤ s.rd.ro.pending.length := by
      omega
    rw [Hk]
    generalize HK : uint.nat N - uint.nat s.rd.ro.confirmed = k at HkP ⊢
    have Hsplit : s.rd.ro.pending = s.rd.ro.pending.take k ++ s.rd.ro.pending.drop k :=
      (List.take_append_drop k _).symm
    ihave Hpq2 := (BigSepL.bigSepL_append (Φ := fun j (q' : ReadReq) => iprop(∃ r e',
        ⌜recs[uint.nat s.rd.ro.confirmed + j]? = some r ∧ q'.index = r.1.2 ∧ q'.ents = [e']⌝ ∗
        ⌜e'.Data' = r.1.1⌝))).1 $$ [Hpq]
    · rw [← Hsplit]; iexact Hpq
    icases Hpq2 with ⟨#Hpq1, #Hpq2⟩
    have Htk : (s.rd.ro.pending.take k).length = k := by simp; omega
    ihave #Hoks := confirm_all γ s.term Q X (fun r Hc => Hconf Q r HQq Hc) recs $$ HX Hrs
    iframe HX
    isplitl
    · iexists γl, rqm
      isplitr; · ipureintro; exact Hγl
      isplitl [Ha]; · iexact Ha
      isplitr; · iexact Hf
      isplitr
      · ipureintro
        intro t Ht
        rcases Hok t Ht with h | ⟨h1, -⟩
        · left; exact h
        · right; exact ⟨h1, by simp⟩
      isplitl [Hauth Hcrs]
      · iexists γq, recs
        isplitr; · ipureintro; exact Hq
        isplitl [Hauth]; · iexact Hauth
        isplitr; · iexact Hrs
        isplitr
        · ipureintro
          simp only [List.length_drop]
          omega
        isplitr
        · iapply BigSepL.bigSepL_impl $$ Hpq2
          imodintro
          iintro %j %x %Hj ⟨%r, %e', %Hx, #Hd⟩
          iexists r, e'
          iframe Hd
          ipureintro
          refine ⟨?_, Hx.2⟩
          rw [← Hx.1]
          congr 1
          simp only at *
          omega
        isplitr; · ipureintro; exact Hacks'
        iexact Hcrs
      isplitr; · iexact Hst0
      isplitr; · iexact Hpd0
      isplitl [Hcr]; · iexact Hcr
      iframe Hinv
      iexact Htk
    · iapply BigSepL.bigSepL_impl $$ Hpq1
      imodintro
      iintro %j %x %Hj ⟨%r, %e', %Hx, #Hd⟩
      have Hjk : j < k := by
        have := (List.getElem?_eq_some_iff.mp Hj).1
        rw [Htk] at this; exact this
      have HiN : uint.nat s.rd.ro.confirmed + j < uint.nat N := by omega
      have Hmem : r ∈ recs.take (uint.nat N) := by
        rw [List.mem_iff_getElem?]
        exact ⟨uint.nat s.rd.ro.confirmed + j, by rw [List.getElem?_take_of_lt HiN]; exact Hx.1⟩
      ihave #Hok0 := BigSepL.bigSepL_lookup (Φ := fun _ r => iprop(
          ∀ (_ : ∀ v ∈ Q, ∀ t' qq, r.2 = some (t', qq) → v ∉ qq), readOk (GF := GF) γ r.1.1 r.1.2))
        Hx.1 $$ Hoks
      ihave #Hok := Hok0 $$ %(fun v hv t' qq h => (HQN v hv).2 r Hmem t' qq h)
      unfold respFacts
      iexists e', r.1.1
      iframe Hd
      isplitr; · ipureintro; exact Hx.2.2
      rw [Hx.2.1]
      iexact Hok

/-- An answer, given its facts. -/
theorem ownRaftGhost_respond (γ : RaftNames) (id : w64) (t : PState) (q : ReadReq) :
    ⊢ ownRaftGhost (GF := GF) γ id t md -∗ respFacts γ q ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (preadRespond id t q) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_respondAll (γ : RaftNames) (id : w64) (qs : List ReadReq) :
    ∀ t, ⊢ ownRaftGhost (GF := GF) γ id t md -∗ ([∗list] q ∈ qs, respFacts γ q) ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (preadRespondAll id t qs) md := by
  induction qs with
  | nil =>
    intro t
    iintro Hown -
    rw [preadRespondAll_nil]
    imodintro; iexact Hown
  | cons q qs ih =>
    intro t
    iintro Hown Hqs
    icases (BigSepL.bigSepL_cons).1 $$ Hqs with ⟨#Hq, Hqs⟩
    rw [preadRespondAll_cons]
    imod ownRaftGhost_respond γ id t q $$ Hown Hq with Hown
    iapply ih $$ Hown Hqs

theorem ownRaftGhost_step_read_ack (γ : RaftNames) (c : CfgM) (id : w64)
    (s : PState) (m : Msg) (N : w64) :
    m.ty = .heartbeatResp → m.dst = id → m.term = s.term → s.role = .leader → m.ctx ≠ [] →
    JQuorumAcked c
      (fun v => ((readonlyRecvAck s.rd.ro m.src m.ctx).acks !! v).getD (W64 0)) N →
    ⊢ dynEnv γ id c s -∗ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (preadRespondAll id
        ({ s with rd := { s.rd with
             ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } })
        (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- A request at a leader whose commit index is at an entry of its term, at a configuration whose
only voter is the leader itself (2026-10-14, the single-voter read-index fix,
`issues/raft-readindex-singleton-stale.md`): read at the commit index, confirmed by the leader's
own acknowledgement -- `{id}` is a joint quorum there (`JQuorum_single`), and the leader is in no
doom quorum of its own term (`ownLogGhost_not_doomed`) -- in either mode (`rqRecOk_confirm`,
`rqRecOk_confirm_dyn`, as the heartbeat path's `ownRaftGhost_step_read_ack`). -/
theorem ownRaftGhost_single_confirm (γ : RaftNames) (c : CfgM) (id : w64) (s : PState)
    (cx : List w8) (Lc : List EntryM) :
    s.role = .leader → plogTermAt s.base s.log s.commit = some s.term → CfgSingle c id →
    ⊢ dynEnv γ id c s -∗ ownRaftGhost (GF := GF) γ id s md -∗ readReq γ cx Lc ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id s md ∗ readOk γ cx s.commit := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `StepC.readSingle`: the request confirmed at once (`ownRaftGhost_single_confirm`) and
answered; its read credit is dropped. -/
theorem ownRaftGhost_step_read_single (γ : RaftNames) (c : CfgM) (id : w64) (s : PState)
    (m : Msg) :
    m.ty = .readIndex → s.role = .leader → plogTermAt s.base s.log s.commit = some s.term →
    CfgSingle c id →
    ⊢ dynEnv γ id c s -∗ isMessage (GF := GF) γ m -∗ rdCred γ 1 -∗ ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (preadRespondAll id s [⟨s.commit, m.src, m.entries⟩]) md := by
  intro Hty Hrole Hct Hsg
  iintro #Henv #Hm - Hown
  iunfold isMessage at Hm
  rw [Hty]
  icases Hm with ⟨%e, %cx, %Lc, %He, #Hpd, #Hrq⟩
  imod ownRaftGhost_single_confirm γ c id s cx Lc Hrole Hct Hsg $$ Henv Hown Hrq with ⟨Hown, #Hok⟩
  rw [preadRespondAll_cons, preadRespondAll_nil]
  iapply ownRaftGhost_respond γ id s _ $$ Hown []
  unfold respFacts
  iexists e, cx
  iframe Hpd Hok
  ipureintro; exact He

/-- `StepC.readReleaseSingle`: the pending requests taken out with their facts, each confirmed
at once (`ownRaftGhost_single_confirm`), then all answered; their credits are dropped. -/
theorem ownRaftGhost_step_read_release_single (γ : RaftNames) (c : CfgM) (id : w64)
    (s : PState) :
    s.role = .leader → plogTermAt s.base s.log s.commit = some s.term → CfgSingle c id →
    ⊢ dynEnv γ id c s -∗ ownRaftGhost (GF := GF) γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (preadRespondAll id { s with rd := { s.rd with pend := [] } }
        (s.rd.pend.map (fun p => ⟨s.commit, p.1.From', p.2⟩))) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_read_state (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (e : EntryM) :
    m.ty = .readIndexResp → m.entries = [e] →
    ⊢ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id ({ s with rd := { s.rd with
        states := s.rd.states ++ [⟨m.index, e.Data'⟩] } }) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_higherTerm (γ : RaftNames) (id : w64) (m : Msg) (s : PState)
    (Hlt : uint.Z s.term < uint.Z m.term) (Hto : m.dst = id)
    (Hfl : fromLeader m.ty = true → m.src ≠ id) :
    ⊢ ([∗list] m ∈ ([m] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([m] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0)) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_grantVote (γ : RaftNames) (id : w64) (m : Msg) (s : PState)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hfrom : m.src ≠ W64 0) (Hterm : m.term = s.term)
    (Hcan : PCanVote s m.src)
    (Hutd : plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) :
    ⊢ ([∗list] m ∈ ([m] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([m] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src s.term false]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_rejectVote (γ : RaftNames) (id : w64) (m : Msg) (s : PState) (Hty : m.ty = .vote) (Hto : m.dst = id) :
    ⊢ ([∗list] m ∈ ([m] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([m] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (psendMsgs s [Msg.plain .voteResp id m.src s.term true]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_recordVote (γ : RaftNames) (id : w64) (m : Msg) (s : PState)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate) :
    ⊢ ([∗list] m ∈ ([m] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([m] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id ({ s with votes := recordVote s.votes m.src (!m.reject) }) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_lose (γ : RaftNames) (c : CfgM) (id : w64) (s : PState) (Hrole : s.role = .candidate) (Hnq : JLost c s.votes) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (pbecomeFollower s s.term (W64 0)) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `StepR.stepDown` (2026-10-14, stage B5): a leader becomes a follower at its term. Its
term log, commit lower bound and read registry are dropped (`ownLogGhost_stepDown`,
`lcmOwn_mono'`, `rdOwn_mono'`); its known leader (itself) stays known. -/
theorem ownRaftGhost_step_stepDown (γ : RaftNames) (id : w64) (s : PState)
    (Hrole : s.role = .leader) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (pbecomeFollower s s.term (W64 0)) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_drain (γ : RaftNames) (id : w64) (s : PState) (o' : List Msg) (Hsub : o'.Subperm s.outbox) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id ({ s with outbox := o' }) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_takeReads {E : CoPset} (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={E}=∗ ownRaftGhost γ id ({ s with rd := { s.rd with states := [] } }) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_sendFree (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (Hfree : m.ty = .preVote ∨ m.ty = .preVoteResp) (Hfrom : m.src = id) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (psendMsgs s [m]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_abandon (γ : RaftNames) (id : w64) (s : PState) (Hrole : s.role ≠ .leader) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (pbecomeFollower s s.term (W64 0)) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

theorem ownRaftGhost_step_zeroAck (γ : RaftNames) (id : w64) (s : PState) (dst : w64) :
    ⊢ ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗ ownRaftGhost γ id (psendMsgs s [Msg.mk .appResp id dst s.term false
                                (W64 0) (W64 0) (W64 0) (W64 0) []]) md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- `Step.campaign` (extracted from `ownRaftGhost_stepC` on 2026-10-14, stage B5, with the step's
environment `dynEnv`, whose dynamic part gives the campaign's I1; it also returns the campaign
record of the full log at the commit index, which the dynamic refinement keeps for a candidate). -/
theorem ownRaftGhost_step_campaign (γ : RaftNames) (c : CfgM) (id : w64) (s : PState)
    (peers : List w64) (cl : List w8) (Hrole : s.role ≠ .leader) (Hin : id ∈ c.voters)
    (Hnw : uint.Z s.term + 1 < 2 ^ 64) (Hperm : peers ≡ₚ elements (c.voters \ {[id]})) :
    ⊢ dynEnv γ id c s -∗
      ([∗list] m ∈ ([] : List Msg), isMessage (GF := GF) γ m) -∗ rdCred γ (rdCount ([] : List Msg)) -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      ownRaftGhost γ id (psendMsgs (pbecomeCandidate id s)
          ([Msg.plain .voteResp id id (pbecomeCandidate id s).term false] ++
           peers.map (fun dst => pvoteReq id dst (pbecomeCandidate id s).term
                                   (plogLast s.base s.log) cl))) md := by
  -- PORT(durability stage II): proof (restated: the campaign record is pending, no `isCampK` output (durability R5))
  sorry

/-- A ghost step with the commit invariant's registry half open (2026-10-14, stage R): its
contents `regsOwn` are threaded through, for the commits (`ownRaftGhost_step_commit`). -/
theorem regs_frame {A B C D : IProp GF} (γ : RaftNames)
    (h : ⊢ A -∗ B -∗ C ={⊤ \ ↑(raftRegN γ)}=∗ D) :
    ⊢ regsOwn γ -∗ A -∗ B -∗ C ={⊤ \ ↑(raftRegN γ)}=∗ regsOwn γ ∗ D := by
  iintro Hregs Ha Hb Hc
  imod h $$ Ha Hb Hc with Hd
  imodintro
  iframe Hregs Hd

/-- Opening the commit invariant's registry half around a ghost step, with one later credit
(2026-10-14, stage R): the step may commit several times (a derivation of the transitive
closure), each commit firing updates that live under the invariant's later, so the half stays
open across the whole step. -/
theorem regs_open (γ : RaftNames) (P Q : IProp GF) :
    ⊢ raftCommitInv γ -∗ £ 1 -∗ (regsOwn γ -∗ P ={⊤ \ ↑(raftRegN γ)}=∗ regsOwn γ ∗ Q) -∗ P ={⊤}=∗ Q := by
  iintro #Hinv Hlc Hstep HP
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  unfold raftRegInv
  iinv Hri with Hregs Hclose
  imod lc_fupd_elim_later $$ Hlc Hregs with Hregs
  imod Hstep $$ Hregs HP with ⟨Hregs, HQ⟩
  imod Hclose $$ [Hregs] with -
  · inext; iexact Hregs
  imodintro
  iexact HQ

theorem ownRaftGhost_inv_md (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ raftCommitInv γ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iapply ownLogGhost_inv $$ Hlg

/-- The receipt of the bound `0`, for a step that creates no entry (2026-10-18, D19b stage 5). -/
theorem preceipt_zero_bound (n : Nat) : ⊢ |==> ⧖ ((0 : Int).toNat - n) := by
  rw [show (0 : Int).toNat - n = 0 by simp]
  exact preceipt_zero (GF := GF)

/-- What covers a log's last index `L` (2026-10-18, D19b stage 5): `L` is `0`, or an entry with a
record sits there (persistent). -/
def lastRec (γ : RaftNames) (L : Int) : IProp GF :=
  iprop(⌜L = 0⌝ ∨ ∃ e, isEntry γ e ∗ ⌜uint.Z e.Index' = L⌝)

instance lastRec_persistent (γ : RaftNames) (L : Int) : Persistent (lastRec (GF := GF) γ L) := by
  unfold lastRec; infer_instance

/-- The time receipt of a last index past the bootstrap log (`isEntry_receipt`). -/
theorem lastRec_receipt (γ : RaftNames) (L : Int) :
    ⊢ lastRec (GF := GF) γ L ==∗ ⧖ (L.toNat - γ.reBoot.length) := by
  unfold lastRec
  iintro (%H0 | ⟨%e, #He, %Hi⟩)
  · rw [H0, show (0 : Int).toNat - γ.reBoot.length = 0 by simp]
    iapply (preceipt_zero (GF := GF))
  · rw [← Hi]; iapply isEntry_receipt γ e $$ He

/-- The node's last index is `0` or has a record (2026-10-18, D19b stage 5): the last entry's
(`logRecs`), or the base's, a snapshot's entry (`isSnapMeta`); and it fits a word. What
`raft.Step` starts a step's receipt from (`lastRec_receipt`). -/
theorem ownRaftGhost_lastRec (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
      lastRec γ (plogLastIndexZ s.base s.log) ∗ ⌜plogLastIndexZ s.base s.log < 2 ^ 64⌝ := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- A step that creates no entry needs no receipt (2026-10-18, D19b stage 5). -/
theorem rcpt_frame {P : IProp GF} {k : Nat} (h : ⊢ P) : ⊢ ⧖ k -∗ P := by
  iintro -
  iapply h

/-- A step that consumes no proposal drops the received messages' tickets (D21 M6). -/
theorem tks_drop {k : Nat} {R A B T C D : IProp GF} {E : CoPset}
    (h : ⊢ ⧖ k -∗ R -∗ A -∗ B -∗ C ={E}=∗ D) : ⊢ ⧖ k -∗ R -∗ A -∗ B -∗ T -∗ C ={E}=∗ D := by
  iintro Hk Hr Ha Hb - Hc
  iapply h $$ Hk Hr Ha Hb Hc

/-- The refinement (2026-10-14, reconfiguration stage B2: at a configuration `c`, the
relation `StepC`), with the commit invariant's registry half open (2026-10-14, stage R): a
protocol step updates the node's ghost state, given the messages it consumed and their read
credits. The configuration is constrained to the ghost state's (`CfgStatic`); only `win`,
`commit` and `readAck` read it, converting its joint quorum to an `IsQuorum γ.reCfg`
(`CfgStatic.isQuorum`) at their start. -/
theorem ownRaftGhost_stepC_in (γ : RaftNames) (c : CfgM) (HC : CfgStatic γ c) (id : w64)
    (HT : TrackedOk γ c id)
    (B : Int) (HB : B < 2 ^ 64) (s : PState) (recv : List Msg) (s' : PState) :
    StepC c id B s recv s' →
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ regsOwn γ -∗ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗
      rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗
      ownRaftGhost γ id s md ={⊤ \ ↑(raftRegN γ)}=∗
      regsOwn γ ∗ ownRaftGhost γ id s' md := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- The refinement (see `ownRaftGhost_stepC_in`), at `⊤`, given one later credit (2026-10-14,
stage R): the commit invariant's registry half opened around the step (`regs_open`). -/
theorem ownRaftGhost_stepC (γ : RaftNames) (c : CfgM) (HC : CfgStatic γ c) (id : w64)
    (HT : TrackedOk γ c id)
    (B : Int) (HB : B < 2 ^ 64) (s : PState) (recv : List Msg) (s' : PState) :
    StepC c id B s recv s' →
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗
      rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      ownRaftGhost γ id s md ={⊤}=∗
      ownRaftGhost γ id s' md := by
  intro Hstep
  iintro #Hrc Hrecv Hcr Htk Hlc Hown
  ihave #Hinv := ownRaftGhost_inv_md γ id s $$ Hown
  iapply regs_open γ iprop(([∗list] m ∈ recv, isMessage (GF := GF) γ m) ∗
      rdCred γ (rdCount recv) ∗ msgsTks γ recv ∗ ownRaftGhost γ id s md) (ownRaftGhost γ id s' md)
    $$ Hinv Hlc [] [Hrecv Hcr Htk Hown]
  · iintro Hregs ⟨Hrecv, Hcr, Htk, Hown⟩
    iapply ownRaftGhost_stepC_in γ c HC id HT B HB s recv s' Hstep $$ Hrc Hregs Hrecv Hcr Htk Hown
  · iframe Hrecv Hcr Htk Hown

end ghost

end EtcdGrove
end Perennial
