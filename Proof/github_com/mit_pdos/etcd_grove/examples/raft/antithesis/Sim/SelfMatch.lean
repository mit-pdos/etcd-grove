/-
Lean-first (no Rocq counterpart).

# Parity B2: a leader's own `Match` within its log along raft's steps (`matchLe_reachP`)

`NodeFactsD`'s `SelfMatchLe` (a leader's own `Match`, and its queued self-acknowledgements' indices,
at most its last index) holds at a `Ready`'s state (`selfMatchLe_ready`): along `ReachP` a leader's
own `Match` is set only by a win (`LeaderMatchOk`: the last index before the win's entry) and raised
only by its own acknowledgements (`Advance`'s, of indices at most the view's last index; a message
from the network is from another node, `MsgShape`), and a leader's log only grows (a proposal, a win)
(`matchLe_reachP`); the `Ready`'s queued self-acknowledgement is at its state's last index
(`qs_self`) (#33 parity B2, Sim round 16).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyKind

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section selfMatch
variable [GooseExts]
variable {kk : NodeK} {c : CfgM} {id : w64}

/-- A leader's own `Match` at most its last index. -/
def MatchLe (id : w64) (s : PState) : Prop :=
  s.role = .leader → uint.Z (matchOf s id) ≤ plogLastIndexZ s.base s.log

theorem matchLe_grow {s t : PState} (hr : t.role = s.role) (hb : t.base = s.base)
    (hl : s.log.length ≤ t.log.length) (hm : t.matched = s.matched) (h : MatchLe id s) :
    MatchLe id t := by
  intro hlt
  have h1 := h (hr.symm.trans hlt)
  unfold matchOf at h1 ⊢
  unfold plogLastIndexZ at h1 ⊢
  rw [hm, hb]
  omega

theorem matchLe_keep {s t : PState} (hr : t.role = s.role) (hb : t.base = s.base) (hl : t.log = s.log)
    (hm : t.matched = s.matched) (h : MatchLe id s) : MatchLe id t :=
  matchLe_grow hr hb (by rw [hl]; exact Nat.le_refl _) hm h

theorem matchLe_pkeep {s t : PState} (h : PKeep s t) : MatchLe id s → MatchLe id t :=
  matchLe_keep h.role h.base h.log h.matched

theorem matchLe_rdKeep {s t : PState} (h : RdKeep s t) : MatchLe id s → MatchLe id t :=
  matchLe_keep h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

theorem matchLe_ne {t : PState} (h : t.role ≠ .leader) : MatchLe id t := fun hl => absurd hl h

theorem plogLastIndexZ_nonneg (b : entryID) (es : List EntryM) : 0 ≤ plogLastIndexZ b es := by
  unfold plogLastIndexZ
  have := uint_Z_nonneg b.index'
  omega

theorem uint_Z_W64_le {z : Int} (h : 0 ≤ z) : uint.Z (W64 z) ≤ z := by
  word

/-- The last index as a word is at most the last index. -/
theorem plastIndex_le (s : PState) : uint.Z (plastIndex s) ≤ plogLastIndexZ s.base s.log :=
  uint_Z_W64_le (plogLastIndexZ_nonneg _ _)

/-- **A win**: the new leader's own `Match` is the last index before its entry. -/
theorem matchLe_win {s s' : PState} (h : WinEnd c id s s') : MatchLe id s' ∧
    plogLastIndexZ s.base s.log ≤ plogLastIndexZ s'.base s'.log ∧ s'.term = s.term := by
  obtain ⟨mt, ms, hlm, -, rfl⟩ := h
  refine ⟨fun _ => ?_, ?_, rfl⟩
  · show uint.Z ((mt !! id).getD (W64 0)) ≤ plogLastIndexZ s.base (s.log ++ [pleaderEntry s])
    rw [hlm.1, Option.getD_some]
    have := plastIndex_le s
    unfold plogLastIndexZ at this ⊢
    simp only [List.length_append, List.length_singleton]
    omega
  · show plogLastIndexZ s.base s.log ≤ plogLastIndexZ s.base (s.log ++ [pleaderEntry s])
    unfold plogLastIndexZ
    simp only [List.length_append, List.length_singleton]
    omega

/-- An acknowledgement raises its sender's `Match` (`max`): the leader's own stays within the log
when the acknowledgement is another node's or of an index within the log. -/
theorem matchLe_raise {s : PState} {m : Msg} {x n : w64} (hr : s.role = .leader)
    (hx : s.matched !! m.src = some x)
    (hidx : m.src = id → uint.Z m.index ≤ plogLastIndexZ s.base s.log) (h : MatchLe id s) :
    MatchLe id { s with matched := <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched,
                        commit := n } := by
  intro _
  have h1 := h hr
  show uint.Z (((<[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched) !! id).getD
    (W64 0)) ≤ plogLastIndexZ s.base s.log
  by_cases hs : m.src = id
  · have hx' : matchOf s id = x := by unfold matchOf; rw [← hs, hx]; rfl
    rw [← hs, lookup_insert, Option.getD_some]
    have h2 := hidx hs
    rw [hx'] at h1
    split <;> omega
  · rw [lookup_insert_ne _ _ hs]; exact h1

/-- **A leader's `MsgAppResp`** keeps its own `Match` within its log (another node's acknowledgement,
or its own of an index within the log), its base, log, term and role. -/
theorem matchLe_appResp {s s' : PState} {m : Msg} (hr : s.role = .leader)
    (hidx : m.src = id → uint.Z m.index ≤ plogLastIndexZ s.base s.log) (h : AppRespEnd c id s m s')
    (hM : MatchLe id s) :
    MatchLe id s' ∧ s'.base = s.base ∧ s'.log = s.log ∧ s'.term = s.term := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, hx, -, hs⟩ | ⟨-, x, n, s2, hx, -, hrel, hs⟩
  · exact ⟨hM, rfl, rfl, rfl⟩
  · have k := (sends_keep hs).1
    exact ⟨matchLe_rdKeep k hM, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, k.1⟩
  · have k := (sends_keep hs).1
    exact ⟨matchLe_rdKeep k (matchLe_raise hr hx hidx hM), k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, k.1⟩
  · have k := (release_keep hrel).1.trans (sends_keep hs).1
    exact ⟨matchLe_rdKeep k (matchLe_raise hr hx hidx hM), k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, k.1⟩

/-- A proposal keeps the leader's own `Match` and grows its log. -/
theorem matchLe_propose {s s' : PState} {m : Msg} (h : ProposeEnd c id s m s') (hM : MatchLe id s) :
    MatchLe id s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, -, rfl⟩
    · exact hM
    · exact matchLe_grow (s := s) rfl rfl (by simp [psendMsgs, pappend]) rfl hM
  · split at h
    · subst h; exact matchLe_pkeep (pkeep_psend _ _) hM
    · subst h; exact hM

/-- **The type switch** on a message other than the node's own acknowledgement keeps a leader's own
`Match` within its log. -/
theorem matchLe_handle {s s' : PState} {m : Msg} (hne : m.ty = .appResp → m.src ≠ id)
    (h : HandleEnd kk c id s m s') (hM : MatchLe id s) : MatchLe id s' := by
  unfold HandleEnd at h
  cases hm : m.ty <;> rw [hm] at h <;> simp only at h
  · -- vote
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact matchLe_keep rfl rfl rfl rfl hM
    · exact matchLe_pkeep (pkeep_psend _ _) hM
  · -- voteResp
    split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact matchLe_keep rfl rfl rfl rfl hM
      · exact (matchLe_win hw).1
      · exact matchLe_ne (by simp [pbecomeFollower])
    · subst h; exact hM
  · -- app
    split at h
    · subst h; exact hM
    · exact matchLe_ne (by rw [(appEnd_facts h).2.2]; simp [padoptLeader])
  · -- appResp
    split at h
    · rename_i hl
      exact (matchLe_appResp hl (fun hs => absurd hs (hne hm)) h hM).1
    · subst h; exact hM
  · -- heartbeat
    split at h
    · subst h; exact hM
    · subst h; exact matchLe_ne (by simp [psendMsgs, padoptLeader])
  · -- heartbeatResp
    split at h
    · exact matchLe_rdKeep (hbResp_keep h).1 hM
    · subst h; exact hM
  · -- propose
    exact matchLe_propose h hM
  · -- snap
    split at h
    · subst h; exact hM
    · rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;>
        exact matchLe_ne (by simp [psendMsgs, padoptLeader])
  · -- preVote
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact matchLe_pkeep (pkeep_psend _ _) hM
  · -- preVoteResp
    split at h
    · rcases h with rfl | ⟨-, peers, -, rfl⟩
      · exact hM
      · exact matchLe_ne (by simp [psendMsgs, pbecomeCandidate])
    · subst h; exact hM
  · -- readIndex
    exact matchLe_pkeep (readIdxEnd_keep h) hM
  · -- readIndexResp
    exact matchLe_rdKeep (readResp_keep h id).1 hM

/-- **A received message** other than the node's own acknowledgement keeps a leader's own `Match`
within its log. -/
theorem matchLe_recv {s s' : PState} {m : Msg} (hne : m.ty = .appResp → m.src ≠ id)
    (h : RecvEnd kk c id s m s') (hM : MatchLe id s) : MatchLe id s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, hst⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact matchLe_handle hne hh hM
  · rcases hst with rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact hM
    · exact matchLe_pkeep (pkeep_psend _ _) hM
    · exact matchLe_pkeep (pkeep_psend _ _) hM
  · exact hM
  · refine matchLe_handle hne hh ?_
    rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact matchLe_ne (by simp [pbecomeFollower])
    · exact hM
    · exact hM

theorem matchLe_campaignSends {s s' : PState} {cl : List w8} (h : CampaignSends c id s cl s') :
    MatchLe id s' := by
  obtain ⟨peers, -, rfl⟩ := h
  exact matchLe_ne (by simp [psendMsgs, pbecomeCandidate])

/-- **A tick** keeps a leader's own `Match` within its log. -/
theorem matchLe_tick {s s' : PState} (h : TickEnd kk c id s s') (hM : MatchLe id s) : MatchLe id s' := by
  rcases h with rfl | ⟨-, -, hce⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact hM
  · exact matchLe_campaignSends hce.sends
  · exact matchLe_ne (by simp [psendMsgs])
  · exact matchLe_pkeep (pkeep_psend _ _) hM
  · exact matchLe_ne (by simp [pbecomeFollower])

/-- What `Advance`'s steps keep from a state of last index `L0` and term `T`: a leader's own `Match`
within its log, the last index at least `L0`, the term. -/
def AdvM (id : w64) (L0 : Int) (T : w64) (s : PState) : Prop :=
  MatchLe id s ∧ L0 ≤ plogLastIndexZ s.base s.log ∧ s.term = T

/-- One step of `Advance`: a self-addressed message of the term, an acknowledgement of an index at
most `L0`. -/
theorem advM_step {L0 : Int} {T : w64} {s s' : PState} {q : Msg} (hi : AdvM id L0 T s)
    (hq : SelfMsg id T q) (hidx : q.ty = .appResp → uint.Z q.index ≤ L0)
    (h : RecvEnd kk c id s q s') : AdvM id L0 T s' := by
  obtain ⟨hqs, -, hqt, -, hty⟩ := hq
  obtain ⟨hM, hL, hT⟩ := hi
  have hh := recvEnd_self hty (hqt.trans hT.symm) h
  unfold HandleEnd at hh
  rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
  · split at hh
    · rename_i hr
      obtain ⟨h1, h2, h3, h4⟩ :=
        matchLe_appResp hr (fun _ => Int.le_trans (hidx hty) hL) hh hM
      exact ⟨h1, by rw [h2, h3]; exact hL, h4.trans hT⟩
    · subst hh; exact ⟨hM, hL, hT⟩
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact ⟨matchLe_keep rfl rfl rfl rfl hM, hL, hT⟩
      · obtain ⟨w1, w2, w3⟩ := matchLe_win hw
        exact ⟨w1, Int.le_trans hL w2, w3.trans hT⟩
      · exact ⟨matchLe_ne (by simp [pbecomeFollower]), hL, hT⟩
    · subst hh; exact ⟨hM, hL, hT⟩

theorem advM_run {L0 : Int} {T : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEnd kk c id s qs s') (hq : ∀ q ∈ qs, SelfMsg id T q)
    (hidx : ∀ q ∈ qs, q.ty = .appResp → uint.Z q.index ≤ L0) (hi : AdvM id L0 T s) :
    AdvM id L0 T s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (fun x hx => hidx x (List.mem_cons_of_mem _ hx))
      (advM_step hi (hq q List.mem_cons_self) (hidx q List.mem_cons_self) hr)

/-- **A leader's own `Match` within its log along `ReachP`**, from the view's: a message received is
from another node (`MsgShape`), the queued self-messages but pre-votes are `SelfMsg`s at the view's
term, its acknowledgements of indices within the view's log. -/
theorem matchLe_reachP {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (hM : MatchLe id v.ps) (hsd : ∀ m ∈ net, m.ty ≠ .readIndex → m.src ≠ m.dst)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg id v.ps.term q)
    (hidx : ∀ q ∈ v.qs, q.ty = .appResp → uint.Z q.index ≤ plogLastIndexZ v.ps.base v.ps.log)
    (hr : ReachP kk c id net xnet v ps₁) : MatchLe id ps₁ := by
  cases hr with
  | stay _ _ => exact hM
  | recv m _ _ _ _ hmn hmd _ _ hO =>
    refine matchLe_recv (fun ht => ?_) hO hM
    have := hsd m hmn (by rw [ht]; decide)
    rw [hmd] at this; exact this
  | recvP m _ _ _ _ _ _ _ hpt _ hO =>
    refine matchLe_recv (fun ht => ?_) hO hM
    rcases hpt with h1 | h1 <;> rw [h1] at ht <;> cases ht
  | tick _ _ _ ht => exact matchLe_tick ht hM
  | propose d _ _ _ hh => exact matchLe_propose hh hM
  | read d _ _ _ hh => exact matchLe_pkeep (readIdxEnd_keep hh) hM
  | advance _ _ _ _ hno ha =>
    exact (advM_run ha (fun q hq => hqs q hq (hno q hq)) hidx ⟨hM, Int.le_refl _, rfl⟩).1
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact hM
    · exact matchLe_campaignSends hcs
  | sends _ _ _ _ hs => exact matchLe_rdKeep (sends_keep hs).1 hM
  | adoptX x _ _ _ _ _ _ => exact matchLe_ne (by simp [pbecomeFollower])
  | campX x p1 _ _ _ _ _ _ _ _ _ hc _ => exact matchLe_campaignSends hc.sends

/-- A queued acknowledgement is a leader's (`QsOk`). -/
theorem QsOk.lead_of_app {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q) (ht : q.ty = .appResp) : v.ps.role = .leader := by
  obtain ⟨-, -, -, ⟨-, ⟨-, hl, -⟩ | ⟨hv, -⟩⟩ | ⟨hp, -⟩⟩ := h
  · exact hl
  · rw [ht] at hv; cases hv
  · rw [ht] at hp; cases hp

/-- A queued acknowledgement is a leader's (`QsOk`, `QsAckW`). -/
theorem qsD_lead {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q ∨ QsAckW n v q) (ht : q.ty = .appResp) : v.ps.role = .leader :=
  h.elim (fun h => h.lead_of_app ht) fun h => h.2.2.2.2.2.1

/-- **`SelfMatchLe` at a `Ready`'s state**, from the view's, along `ReachP` (`matchLe_reachP`), the
`Ready`'s queued self-acknowledgement at its state's last index (`qs_self`). -/
theorem selfMatchLe_ready {R : RunCfg} {n : Fin R.N} {net : List Msg} {xnet : List XMsg}
    {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hsm : SelfMatchLe (nodeId n) v.ps v.qs) (hql : ∀ q ∈ v.qs, q.ty = .appResp → v.ps.role = .leader)
    (hr : ReachP kk c (nodeId n) net xnet v r₁.p) (hro : ReadyOutP R n v r₁ rd)
    (hX : v.ps.outbox = []) (hlo : v.ps.role ≠ .leader → v.ps.lead ≠ nodeId n)
    (hin : ∀ m ∈ net, RdTy m.ty → InMsg m) (hsd : ∀ m ∈ net, m.ty ≠ .readIndex → m.src ≠ m.dst)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg (nodeId n) v.ps.term q) :
    SelfMatchLe (nodeId n) (accepted r₁).p rd.qs := by
  have hM : MatchLe (nodeId n) r₁.p :=
    matchLe_reachP (fun hl => (hsm hl).1) hsd hqs (fun q hq ht => (hsm (hql q hq ht)).2 q hq ht) hr
  have hso := selfOut_reach hr hX hlo hin hsd hqs
  intro hl
  have hl' : r₁.p.role = .leader := hl
  refine ⟨hM hl', fun q hq _ => ?_⟩
  rcases (qs_self hro hso (by rw [hl']; decide) q hq).2 with ⟨-, rfl⟩ | ⟨hc, -⟩
  · exact plastIndex_le r₁.p
  · rw [hl'] at hc; cases hc

end selfMatch

end AntSim
end EtcdGrove
end Perennial
