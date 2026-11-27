/-
Lean-first (no Rocq counterpart).

# The read requests' numbers along `Reach` (antithesis parity B1, reads on)

`readOk_reach`: `NodeFacts`' last conjunct (`ReadOk`: every deferred read request's entries, and a
leader's queued requests' entries, within `2 ^ 61`, each queued request at an index at most the
commit) at the state a `Ready` is taken at. A request enters only by `ReadIdxEnd`, from a received
`MsgReadIndex` (its numbers within `2 ^ 61`, `MsgMask`) or the local `readMsg` (no numbers), queued
at the commit index of the moment; commits only grow (`commit_reachP`); a new role resets the
queue (`rdNL`).

`readNums_reach`: what `readyMsgNums` asks of the view's read requests (`ReadNums (2 ^ 61) v.ps`),
from `ReadOk` and the commit of the state reached within `2 ^ 61` (`StateNums`).
`causeReadNums`: the drain's cause, when a `MsgReadIndex`, has all its numbers within `2 ^ 61`
(it is on the network, `MsgMask`).

(The lead's first statement, `ReadNums (2 ^ 61) v.ps` itself in `NodeFacts`, could not be kept:
a quiet step, `Quiet.noReady`, defers a received request with no number fact about it, and a
queued request's index is a commit no `Sim` fact bounds.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

section readnums
variable [GooseExts]
variable {kk : NodeK}

/-! ## Commits only grow -/

theorem commit_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hsc : RdTy m.ty)
    (hh : HandleEnd kk c id s m s') : uint.Z s.commit ≤ uint.Z s'.commit := by
  unfold HandleEnd at hh
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at hh; simp only at hh; rw [(readIdxEnd_keep hh).commit]; exact Int.le_refl _
  · rw [hty] at hh; simp only at hh
    split at hh
    · rcases hh with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact Int.le_refl _
    · subst hh; exact Int.le_refl _
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;>
    simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact Int.le_refl _
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact Int.le_refl _
      · obtain ⟨mt, ms, -, -, rfl⟩ := hw; exact Int.le_refl _
      · exact Int.le_refl _
    · subst hh; exact Int.le_refl _
  · split at hh
    · subst hh; exact Int.le_refl _
    · rcases hh with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩
      · exact Int.le_refl _
      · exact plogCommitTo_ge _ _
      · exact Int.le_refl _
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, hn, hs'⟩ | ⟨-, x, n, s2, -, hn, hrel, hs'⟩
      · exact Int.le_refl _
      · obtain ⟨ms, -, rfl⟩ := hs'; exact Int.le_refl _
      · obtain ⟨ms, -, rfl⟩ := hs'
        show uint.Z s.commit ≤ uint.Z n
        rcases hn with rfl | hn
        · exact Int.le_refl _
        · exact Int.le_of_lt hn.1
      · obtain ⟨ms, -, rfl⟩ := hs'
        show uint.Z s.commit ≤ uint.Z s2.commit
        rw [(releaseEnd_keep hrel).commit]; exact Int.le_of_lt hn.1
    · subst hh; exact Int.le_refl _
  · split at hh
    · subst hh; exact Int.le_refl _
    · subst hh; exact plogCommitTo_ge _ _
  · split at hh
    · obtain ⟨s2, hs', ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := hh
      · obtain ⟨ms, -, rfl⟩ := hs'; exact Int.le_refl _
      · obtain ⟨ms, -, rfl⟩ := hs'
        rw [(readAckEnd_keep ha).commit]; exact Int.le_refl _
    · subst hh; exact Int.le_refl _
  · unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact Int.le_refl _
    · split at hh
      · subst hh; exact Int.le_refl _
      · subst hh; exact Int.le_refl _

theorem commit_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hsc : RdTy m.ty)
    (hr : RecvEnd kk c id s m s') : uint.Z s.commit ≤ uint.Z s'.commit := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact commit_handle hsc hh
  · exact Int.le_refl _
  · exact Int.le_refl _
  · exact Int.le_refl _
  · exact Int.le_refl _
  · have h1 : s1.commit = s.commit := by
      rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    rw [← h1]; exact commit_handle hsc hh

theorem commit_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (ha : AdvanceEnd kk c id s qs s') :
    uint.Z s.commit ≤ uint.Z s'.commit := by
  induction ha with
  | nil => exact Int.le_refl _
  | cons s s1 s' q qs hr _ ih =>
    have hty := hq q (List.mem_cons_self ..)
    refine Int.le_trans (commit_recv ?_ hr) (ih fun x hx => hq x (List.mem_cons_of_mem _ hx))
    rcases hty with h' | h' <;> simp [RdTy, S4Ty, h']

/-- **Commits only grow along `ReachP`.** -/
theorem commit_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView}
    {ps₁ : PState}
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .appResp ∨ q.ty = .voteResp)
    (hr : ReachP kk c id net xnet v ps₁) : uint.Z v.ps.commit ≤ uint.Z ps₁.commit := by
  cases hr with
  | stay _ => exact Int.le_refl _
  | recv m _ _ _ _ _ _ _ hty hO => exact commit_recv hty hO
  | recvP m _ _ _ _ _ _ _ hpt _ hP =>
    rcases recvEnd_pre hpt hP with rfl | ⟨-, -, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ |
        ⟨-, -, -, -, hcs⟩
    · exact Int.le_refl _
    · exact Int.le_refl _
    · exact Int.le_refl _
    · exact Int.le_refl _
    · exact Int.le_refl _
    · obtain ⟨peers, -, rfl⟩ := hcs; exact Int.le_refl _
  | tick _ _ _ ht =>
    rcases ht with rfl | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      exact Int.le_refl _
  | propose d _ _ _ hh =>
    unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact Int.le_refl _
    · split at hh
      · subst hh; exact Int.le_refl _
      · subst hh; exact Int.le_refl _
  | read d _ _ _ hh => rw [(readIdxEnd_keep hh).commit]; exact Int.le_refl _
  | advance _ _ _ _ hno ha => exact commit_adv (fun q hq => hqs q hq (hno q hq)) ha
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact Int.le_refl _
    · obtain ⟨peers, -, rfl⟩ := hcs; exact Int.le_refl _
  | sends _ _ _ _ hs => obtain ⟨ms, -, rfl⟩ := hs; exact Int.le_refl _
  | adoptX x _ _ _ _ _ _ => exact Int.le_refl _
  | campX x p1 _ _ _ _ _ _ _ hp1 _ hc =>
    obtain ⟨-, peers, -, rfl⟩ := hc
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact Int.le_refl _

/-! ## `ReadOk` along `Reach` -/

theorem ReadOk.of {s t : PState} (h : ReadOk s) (hp : t.rd.pend = s.rd.pend)
    (hc : uint.Z s.commit ≤ uint.Z t.commit)
    (hro : t.role = .leader → s.role = .leader ∧ ∀ q ∈ t.rd.ro.pending, q ∈ s.rd.ro.pending) :
    ReadOk t :=
  ⟨fun p hp' => h.1 p (hp ▸ hp'), fun hr q hq =>
    have h2 := h.2 (hro hr).1 q ((hro hr).2 q hq)
    ⟨Int.le_trans h2.1 hc, h2.2⟩⟩

theorem ReadOk.nl {s t : PState} (h : ReadOk s) (hp : t.rd.pend = s.rd.pend)
    (hr : t.role ≠ .leader) : ReadOk t :=
  ⟨fun p hp' => h.1 p (hp ▸ hp'), fun h' => absurd h' hr⟩

theorem ReadOk.ro0 {s t : PState} (h : ReadOk s) (hp : t.rd.pend = s.rd.pend)
    (hro : t.rd.ro.pending = []) : ReadOk t :=
  ⟨fun p hp' => h.1 p (hp ▸ hp'), fun _ q hq => by rw [hro] at hq; cases hq⟩

theorem readOk_respondAll {id : w64} {s : PState} {qs : List ReadReq} (h : ReadOk s) :
    ReadOk (preadRespondAll id s qs) := by
  obtain ⟨-, hk, -⟩ := preadRespondAll_out id s qs
  have hrd := preadRespondAll_rd id s qs
  exact h.of hrd.1 (by rw [hk.commit]; exact Int.le_refl _)
    fun hr => ⟨hk.role.symm.trans hr, fun q hq => by rw [hrd.2] at hq; exact hq⟩

/-- A read request's step keeps `ReadOk`: deferred with its entries, answered, queued at the
commit index, or forwarded. -/
theorem readOk_readIdx {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadOk s)
    (hm : EntNums (2 ^ 61) m.entries) (hR : ReadIdxEnd c id s m s') : ReadOk s' := by
  unfold ReadIdxEnd at hR
  split at hR
  · rcases hR with ⟨-, pm, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, ms, -, rfl⟩
    · refine ⟨fun p hp => ?_, h.2⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact h.1 p hp
      · rw [List.mem_singleton.mp hp]; exact hm
    · exact readOk_respondAll h
    · refine ⟨h.1, fun hr q hq => ?_⟩
      change q ∈ (readonlyArrive s.rd.ro id _).pending at hq
      rw [readonlyArrive_pending] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact h.2 hr q hq
      · rw [List.mem_singleton.mp hq]; exact ⟨Int.le_refl _, hm⟩
  · split at hR
    · subst hR; exact h
    · subst hR; exact h

/-- The deferred reads' release at a leader: each queued at the commit index. -/
theorem readOk_release {c : CfgM} {id : w64} {X s2 : PState} (h : ReadOk X)
    (hr : X.role = .leader) (hR : ReleaseEnd c id X s2) : ReadOk s2 := by
  rcases hR with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨fun p hp => (by cases hp), fun _ q hq => ?_⟩
    change q ∈ (readonlyRelease X.rd.ro id X.commit X.rd.pend).pending at hq
    rw [readonlyRelease_pending] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h.2 hr q hq
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact ⟨Int.le_refl _, h.1 p hp⟩
  · exact readOk_respondAll (s := { X with rd := { X.rd with pend := [] } })
      ⟨fun p hp => (by cases hp), h.2⟩

theorem readOk_readAck {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadOk s)
    (hR : ReadAckEnd c id s m s') : ReadOk s' := by
  rcases hR with ⟨-, rfl⟩ | ⟨N', -, rfl⟩
  · refine h.of rfl (Int.le_refl _) fun hr => ⟨hr, fun q hq => ?_⟩
    change q ∈ (readonlyRecvAck s.rd.ro m.src m.ctx).pending at hq
    rwa [readonlyRecvAck_pending] at hq
  · refine readOk_respondAll (h.of rfl (Int.le_refl _) fun hr => ⟨hr, fun q hq => ?_⟩)
    have := readonlyAdvance_pending _ N' q hq
    rwa [readonlyRecvAck_pending] at this

theorem readOk_sends {c : CfgM} {id : w64} {X s' : PState} (h : ReadOk X) (hs : SendsEnd c id X s') :
    ReadOk s' := by
  obtain ⟨ms, -, rfl⟩ := hs; exact h

/-- A leader's commit raised (`Match` and commit changed): the queue kept. -/
theorem readOk_commit {s : PState} {mt : GMap w64 w64} {n : w64} (h : ReadOk s)
    (hn : uint.Z s.commit ≤ uint.Z n) : ReadOk { s with matched := mt, commit := n } :=
  h.of rfl hn fun hr => ⟨hr, fun _ hq => hq⟩

/-- The type switch keeps `ReadOk` (as `readSrc_handle`; a leader's commit only grows). -/
theorem readOk_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadOk s)
    (hsc : RdTy m.ty) (hm : m.ty = .readIndex → EntNums (2 ^ 61) m.entries)
    (hh : HandleEnd kk c id s m s') : ReadOk s' := by
  unfold HandleEnd at hh
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at hh; simp only at hh; exact readOk_readIdx h (hm hty) hh
  · rw [hty] at hh; simp only at hh
    split at hh
    · rcases hh with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h
    · subst hh; exact h
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;>
    simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact h
      · obtain ⟨mt, ms, -, -, rfl⟩ := hw; exact h.ro0 rfl rfl
      · exact h.nl rfl (by simp [pbecomeFollower])
    · subst hh; exact h
  · split at hh
    · subst hh; exact h
    · rcases hh with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩ <;>
        exact h.nl rfl (by simp [psendMsgs, padoptLeader])
  · split at hh
    · rename_i hr
      rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, hn, hs'⟩ | ⟨-, x, n, s2, -, hn, hrel, hs'⟩
      · exact h
      · exact readOk_sends h hs'
      · refine readOk_sends (readOk_commit h ?_) hs'
        rcases hn with rfl | hn
        · exact Int.le_refl _
        · exact Int.le_of_lt hn.1
      · exact readOk_sends (readOk_release (readOk_commit h (Int.le_of_lt hn.1)) hr hrel) hs'
    · subst hh; exact h
  · split at hh
    · subst hh; exact h
    · subst hh; exact h.nl rfl (by simp [psendMsgs, padoptLeader])
  · split at hh
    · obtain ⟨s2, hs', ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := hh
      · exact readOk_sends h hs'
      · exact readOk_readAck (readOk_sends h hs') ha
    · subst hh; exact h
  · unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact h
    · split at hh
      · subst hh; exact h
      · subst hh; exact h

theorem readOk_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadOk s)
    (hsc : RdTy m.ty) (hm : m.ty = .readIndex → EntNums (2 ^ 61) m.entries)
    (hr : RecvEnd kk c id s m s') : ReadOk s' := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact readOk_handle h hsc hm hh
  · exact h
  · exact h
  · exact h
  · exact h
  · refine readOk_handle ?_ hsc hm hh
    rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact h.nl rfl (by simp [pbecomeFollower])
    · exact h
    · exact h

theorem readOk_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (h : ReadOk s)
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (ha : AdvanceEnd kk c id s qs s') :
    ReadOk s' := by
  induction ha with
  | nil => exact h
  | cons s s1 s' q qs hr _ ih =>
    have hty := hq q (List.mem_cons_self ..)
    refine ih ?_ (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    refine readOk_recv h ?_ (fun h' => by rcases hty with h'' | h'' <;> rw [h''] at h' <;> cases h') hr
    rcases hty with h' | h' <;> simp [RdTy, S4Ty, h']

/-- **`ReadOk` along `ReachP`**: a request enters only by `ReadIdxEnd`, from a received message
(its numbers within `2 ^ 61`, `hen`) or the local `readMsg`; queued at the commit, which only
grows; a new role resets the queue. -/
theorem readOk_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView}
    {ps₁ : PState} (h : ReadOk v.ps)
    (hen : ∀ m ∈ net, m.ty = .readIndex → MsgNums (2 ^ 61) m)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .appResp ∨ q.ty = .voteResp)
    (hr : ReachP kk c id net xnet v ps₁) : ReadOk ps₁ := by
  cases hr with
  | stay _ => exact h
  | recv m _ _ _ _ hmn _ _ hty hO =>
    exact readOk_recv h hty (fun ht => (hen m hmn ht).2.2.2) hO
  | recvP m _ _ _ _ _ _ _ hpt _ hP =>
    rcases recvEnd_pre hpt hP with rfl | ⟨-, -, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ |
        ⟨-, -, -, -, hcs⟩
    · exact h
    · exact h
    · exact h
    · exact h
    · exact h.nl rfl (by simp [pbecomeFollower])
    · obtain ⟨peers, -, rfl⟩ := hcs; exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])
  | tick _ _ _ ht =>
    rcases ht with rfl | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h
    · exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])
    · exact h.nl rfl (by simp [psendMsgs])
    · exact h
    · exact h.nl rfl (by simp [pbecomeFollower])
  | propose d _ _ _ hh =>
    unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact h
    · split at hh
      · subst hh; exact h
      · subst hh; exact h
  | read d _ _ _ hh => exact readOk_readIdx h (msgNums_readMsg (by decide) d).2.2.2 hh
  | advance _ _ _ _ hno ha => exact readOk_adv h (fun q hq => hqs q hq (hno q hq)) ha
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact h
    · obtain ⟨peers, -, rfl⟩ := hcs; exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])
  | sends _ _ _ _ hs => exact readOk_sends h hs
  | adoptX x _ _ _ _ _ _ => exact h.nl rfl (by simp [pbecomeFollower])
  | campX x p1 _ _ _ _ _ _ _ hp1 _ hc =>
    obtain ⟨-, peers, -, rfl⟩ := hc
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])

/-- **`ReadOk` at the state a `Ready` is taken at** (`NodeFacts`' last conjunct, `readOk_reachP`):
the view's, a received `MsgReadIndex`'s numbers by `MsgMask`. For the runs a mask below `mskB1`
admits. -/
theorem readOk_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    ReadOk r₁.p :=
  readOk_reachP hv.facts.readOk (fun m hmn => (hnet.2.2.2.2.1 m hmn).2.2.2.2)
    (fun q hq hne => ((hv.qs q hq).self hne).2.2.2.2) (ReachIn.toP hmsk hin hnet hv hr)

/-- **Commits only grow along `ReachIn`** (`commit_reachP`). -/
theorem commit_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    uint.Z v.ps.commit ≤ uint.Z r₁.p.commit :=
  commit_reachP (fun q hq hne => ((hv.qs q hq).self hne).2.2.2.2) (ReachIn.toP hmsk hin hnet hv hr)

/-! ## What `readyMsgNums` asks, with reads on -/

/-- **The view's read requests within `2 ^ 61`** (`readyMsgNums`' `ReadNums` premise): the
entries by `ReadOk` (`NodeFacts`), a leader's queued requests at an index at most its commit, at
most the commit of the state reached (`commit_reach`), within `2 ^ 61` (`StateNums`). -/
theorem readNums_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hs : StateNums (2 ^ 61) r₁.p) : ReadNums (2 ^ 61) v.ps := by
  have hc := commit_reach hmsk hin hnet hv hr
  have hc' := hs.2.2.2.1
  obtain ⟨h1, h2⟩ := hv.facts.readOk
  exact ⟨h1, fun hl r hr' => ⟨Int.lt_of_le_of_lt (Int.le_trans (h2 hl r hr').1 hc) hc', (h2 hl r hr').2⟩⟩

/-- **The drain's cause, a `MsgReadIndex`, has its numbers within `2 ^ 61`** (it is on the
network, `NodeOk`, under the mask, `MsgMask`). -/
theorem causeReadNums {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {n : Fin R.N} {v : NodeView} (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) :
    ∀ m, v.cause = some m → m.ty = .readIndex → MsgNums (2 ^ 61) m :=
  fun m hm => (hnet.2.2.2.2.1 m (hv.cause m hm).1).2.2.2.2

end readnums

end AntSim
end EtcdGrove
end Perennial
