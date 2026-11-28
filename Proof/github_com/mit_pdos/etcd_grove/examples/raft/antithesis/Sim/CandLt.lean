/-
Lean-first (no Rocq counterpart).

# Parity B2: a candidate's log is of earlier terms along raft's steps (`candLt_reachP`)

`NodeFactsD`'s `CandLt` (a candidate's entries are of terms below its own) holds along `ReachP`: a
step that ends at a candidate either keeps the role, the log and the term (`CandKeep`: every arm but a
campaign; a step that adds entries ends at a non-candidate or starts at one: a leader's append, a
follower's `AppEnd`, a win), or is a campaign (`CampaignSends`: the term raised by one above the log's
terms, the log unchanged), which needs the log's terms at most the term and the term below the top at
the state it starts from (raft's `rawNode_logTerms` and its term ceiling) (#33 parity B2, Sim round 14).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section candLt
variable [GooseExts]
variable {kk : NodeK}

/-- A step to `s'` that ends at a candidate started at one, with the same log and term. -/
def CandKeep (s s' : PState) : Prop :=
  s'.role = .candidate → s.role = .candidate ∧ s'.log = s.log ∧ s'.term = s.term

theorem CandKeep.candLt {s s' : PState} (h : CandKeep s s') (hc : CandLt s) : CandLt s' := by
  intro hr e he
  obtain ⟨h1, h2, h3⟩ := h hr
  rw [h3]; rw [h2] at he; exact hc h1 e he

theorem CandKeep.trans {s t u : PState} (h1 : CandKeep s t) (h2 : CandKeep t u) : CandKeep s u := by
  intro hr
  obtain ⟨a, b, c⟩ := h2 hr
  obtain ⟨a', b', c'⟩ := h1 a
  exact ⟨a', b.trans b', c.trans c'⟩

theorem candKeep_pkeep {s t : PState} (h : PKeep s t) : CandKeep s t := fun hr =>
  ⟨by rw [← h.role]; exact hr, h.log, h.term⟩

theorem candKeep_refl (s : PState) : CandKeep s s := fun hr => ⟨hr, rfl, rfl⟩

theorem candKeep_ne {s s' : PState} (h : s'.role ≠ .candidate) : CandKeep s s' := fun hr => absurd hr h

/-- **A campaign** from a state whose log's terms are at most its term, below the top: the new term
is above them all. -/
theorem candLt_campaign {c : CfgM} {id : w64} {s s' : PState} {cl : List w8}
    (hle : ∀ e ∈ s.log, uint.Z e.Term' ≤ uint.Z s.term) (hb : uint.Z s.term < 2 ^ 64 - 1)
    (h : CampaignSends c id s cl s') : CandLt s' := by
  obtain ⟨peers, -, rfl⟩ := h
  intro _ e he
  have := hle e he
  show uint.Z e.Term' < uint.Z (s.term + W64 1)
  word

/-- A proposal keeps a candidate (a candidate drops it; a leader's append stays a leader). -/
theorem propose_candKeep {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ProposeEnd c id s m s') :
    CandKeep s s' := by
  unfold ProposeEnd at h
  split at h
  · rename_i hl
    rcases h with rfl | ⟨es, ms, -, -, rfl⟩
    · exact candKeep_refl _
    · exact candKeep_ne (by show s.role ≠ _; rw [hl]; simp)
  · split at h
    · subst h; exact candKeep_pkeep (pkeep_psend _ _)
    · subst h; exact candKeep_refl _

/-- **The type switch keeps a candidate** but on a pre-vote response (whose win campaigns). -/
theorem handle_candKeep {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hne : m.ty ≠ .preVoteResp)
    (h : HandleEnd kk c id s m s') : CandKeep s s' := by
  unfold HandleEnd at h
  cases hm : m.ty <;> rw [hm] at h <;> simp only at h
  · -- vote
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact fun hr => ⟨hr, rfl, rfl⟩
    · exact candKeep_pkeep (pkeep_psend _ _)
  · -- voteResp
    split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact fun hr => ⟨hr, rfl, rfl⟩
      · exact candKeep_ne (by simp [psendMsgs, pwinState, pappend, pbecomeLeader])
      · exact candKeep_ne (by simp [pbecomeFollower])
    · subst h; exact candKeep_refl _
  · -- app
    split at h
    · subst h; exact candKeep_refl _
    · exact candKeep_ne (by rw [(appEnd_facts h).2.2]; simp [padoptLeader])
  · -- appResp
    split at h
    · rename_i hl
      have hro : s'.role = s.role := by
        rcases h with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, n, -, -, ms, -, rfl⟩ |
            ⟨-, x, n, s2, -, -, hrel, ms, -, rfl⟩
        · rfl
        · rfl
        · rfl
        · exact (releaseEnd_keep hrel).role
      exact candKeep_ne (by rw [hro, hl]; simp)
    · subst h; exact candKeep_refl _
  · -- heartbeat
    split at h
    · subst h; exact candKeep_refl _
    · subst h; exact candKeep_ne (by simp [psendMsgs, padoptLeader])
  · -- heartbeatResp
    split at h
    · rename_i hl
      obtain ⟨s2, ⟨ms, -, rfl⟩, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact candKeep_ne (by show s.role ≠ _; rw [hl]; simp)
      · exact candKeep_ne (by rw [(readAckEnd_keep ha).role]; show s.role ≠ _; rw [hl]; simp)
    · subst h; exact candKeep_refl _
  · -- propose
    exact propose_candKeep h
  · -- snap
    split at h
    · subst h; exact candKeep_refl _
    · rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;>
        exact candKeep_ne (by simp [psendMsgs, padoptLeader])
  · -- preVote
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact candKeep_pkeep (pkeep_psend _ _)
  · exact absurd hm hne
  · -- readIndex
    exact candKeep_pkeep (readIdxEnd_keep h)
  · -- readIndexResp
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact candKeep_pkeep (pkeep_rd _ _)
      · exact candKeep_refl _
      · exact candKeep_refl _
    · subst h; exact candKeep_refl _

/-- **A received message keeps a candidate** but a pre-vote response. -/
theorem recv_candKeep {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hne : m.ty ≠ .preVoteResp)
    (hr : RecvEnd kk c id s m s') : CandKeep s s' := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact handle_candKeep hne hh
  · exact candKeep_refl _
  · exact candKeep_pkeep (pkeep_psend _ _)
  · exact candKeep_pkeep (pkeep_psend _ _)
  · exact candKeep_refl _
  · have h2 := handle_candKeep hne hh
    rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact candKeep_ne fun hr => by
        obtain ⟨h1, -, -⟩ := h2 hr
        simp [pbecomeFollower] at h1
    · exact h2
    · exact h2

/-- `Advance`'s queued messages, none a pre-vote response, keep a candidate. -/
theorem adv_candKeep {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hq : ∀ q ∈ qs, q.ty ≠ .preVoteResp) (ha : AdvanceEnd kk c id s qs s') : CandKeep s s' := by
  induction ha with
  | nil => exact candKeep_refl _
  | cons s s1 s' q qs hr _ ih =>
    exact (recv_candKeep (hq q List.mem_cons_self) hr).trans
      (ih fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- **`CandLt` along `ReachP`**, from the view's, given the view's log terms at most its term and its
term below the top (what a campaign reads). -/
theorem candLt_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView}
    {ps₁ : PState} (h : CandLt v.ps)
    (hle : ∀ e ∈ v.ps.log, uint.Z e.Term' ≤ uint.Z v.ps.term) (hb : uint.Z v.ps.term < 2 ^ 64 - 1)
    (hr : ReachP kk c id net xnet v ps₁) : CandLt ps₁ := by
  cases hr with
  | stay _ => exact h
  | recv m _ _ _ _ _ _ _ hty hO =>
    refine (recv_candKeep (fun h' => ?_) hO).candLt h
    rw [h'] at hty; simp [RdTy, S4Ty] at hty
  | recvP m _ _ _ _ _ _ _ hpt _ hP =>
    rcases recvEnd_pre hpt hP with rfl | ⟨-, -, rfl⟩ | ⟨-, hpv⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, -, hcs⟩
    · exact h
    · exact (candKeep_pkeep (pkeep_psend _ _)).candLt h
    · rcases hpv with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact (candKeep_pkeep (pkeep_psend _ _)).candLt h
    · exact (candKeep_ne (by simp [pbecomeFollower])).candLt h
    · exact candLt_campaign hle hb hcs
  | tick _ _ _ ht =>
    rcases ht with rfl | ⟨-, -, hce⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h
    · exact candLt_campaign hle hb hce.sends
    · exact (candKeep_ne (by simp [psendMsgs])).candLt h
    · exact (candKeep_pkeep (pkeep_psend _ _)).candLt h
    · exact (candKeep_ne (by simp [pbecomeFollower])).candLt h
  | propose d _ _ _ hh => exact (propose_candKeep hh).candLt h
  | read d _ _ _ hh => exact (candKeep_pkeep (readIdxEnd_keep hh)).candLt h
  | advance _ _ _ _ hno ha => exact (adv_candKeep hno ha).candLt h
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact h
    · exact candLt_campaign hle hb hcs
  | sends _ _ _ _ hs =>
    obtain ⟨ms, -, rfl⟩ := hs
    exact (candKeep_pkeep (pkeep_psend _ _)).candLt h
  | adoptX x _ _ _ _ _ _ => exact (candKeep_ne (by simp [pbecomeFollower])).candLt h
  | campX x p1 _ _ _ _ _ _ _ hp1 _ hc hxle =>
    rcases hp1 with ⟨hlt, rfl⟩ | ⟨-, rfl⟩
    · exact absurd hxle (by omega)
    · exact candLt_campaign hle hb hc.sends

end candLt

end AntSim
end EtcdGrove
end Perennial
