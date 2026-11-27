/-
Lean-first (no Rocq counterpart). #33 parity B1 (lead-approved 11-27): **a `Ready`'s read states'
indices within `2 ^ 61`** (the drain's `read` report's numbers, `evRead`'s `NumsOk`). The view has
none (`NodeFacts.states0`); along `ReachP` a read state is added by a leader's local answer
(`preadRespond`), at a queued request's index, at most the commit then (`ReadOk`), which only grows
(`commit_handle`), or by a follower's `MsgReadIndexResp`, at the message's index (`NetOk`'s last
conjunct); the commit of the state reached is within `2 ^ 61` (`StateNums`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadNums

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

section readstates
variable [GooseExts]
variable {kk : NodeK}

/-- Every read state at an index at most the commit, or within `2 ^ 61`. -/
def StOk (s : PState) : Prop :=
  ∀ st ∈ s.rd.states, uint.Z st.Index' ≤ uint.Z s.commit ∨ uint.Z st.Index' < 2 ^ 61

theorem StOk.of {s t : PState} (h : StOk s)
    (hst : ∀ st ∈ t.rd.states, st ∈ s.rd.states ∨ uint.Z st.Index' ≤ uint.Z t.commit ∨
      uint.Z st.Index' < 2 ^ 61)
    (hc : uint.Z s.commit ≤ uint.Z t.commit) : StOk t := by
  intro st hs
  rcases hst st hs with h1 | h1 | h1
  · exact (h st h1).imp_left fun h' => Int.le_trans h' hc
  · exact .inl h1
  · exact .inr h1

theorem respondAll_states (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).commit = s.commit ∧
      ∀ st ∈ (preadRespondAll id s qs).rd.states, st ∈ s.rd.states ∨ ∃ q ∈ qs, st.Index' = q.index := by
  induction qs generalizing s with
  | nil => exact ⟨rfl, fun st h => .inl h⟩
  | cons r qs ih =>
    rw [preadRespondAll_cons]
    obtain ⟨hc, hs⟩ := ih (preadRespond id s r)
    have hc1 : (preadRespond id s r).commit = s.commit := by
      unfold preadRespond; split
      · split <;> rfl
      · rfl
    have hs1 : ∀ st ∈ (preadRespond id s r).rd.states, st ∈ s.rd.states ∨ st.Index' = r.index := by
      unfold preadRespond; split
      · split
        · intro st h
          simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact .inl h
          · exact .inr rfl
        · exact fun st h => .inl h
      · exact fun st h => .inl h
    refine ⟨hc.trans hc1, fun st h => ?_⟩
    rcases hs st h with h | ⟨q, hq, he⟩
    · rcases hs1 st h with h | h
      · exact .inl h
      · exact .inr ⟨r, List.mem_cons_self, h⟩
    · exact .inr ⟨q, List.mem_cons_of_mem _ hq, he⟩

/-- A local answer at indices at most the commit keeps `StOk`. -/
theorem stOk_respondAll {id : w64} {s : PState} {qs : List ReadReq} (h : StOk s)
    (hq : ∀ q ∈ qs, uint.Z q.index ≤ uint.Z s.commit) : StOk (preadRespondAll id s qs) := by
  obtain ⟨hc, hs⟩ := respondAll_states id s qs
  refine h.of (fun st hst => ?_) (by rw [hc]; exact Int.le_refl _)
  rcases hs st hst with h1 | ⟨q, hq', he⟩
  · exact .inl h1
  · exact .inr (.inl (by rw [hc, he]; exact hq q hq'))

theorem readonlyAdvance_out (r : ReadOnly) (N : w64) : ∀ q ∈ (readonlyAdvance r N).2, q ∈ r.pending := by
  intro q hq
  unfold readonlyAdvance at hq
  split at hq
  · cases hq
  · exact List.mem_of_mem_take hq

theorem StOk.keep {s t : PState} (h : StOk s) (hs : t.rd.states = s.rd.states)
    (hc : uint.Z s.commit ≤ uint.Z t.commit) : StOk t :=
  h.of (fun st hst => .inl (hs ▸ hst)) hc

/-- A read request's step: deferred, answered at the commit, queued, or forwarded. -/
theorem stOk_readIdx {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : StOk s)
    (hR : ReadIdxEnd c id s m s') : StOk s' := by
  unfold ReadIdxEnd at hR
  split at hR
  · rcases hR with ⟨-, pm, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, ms, -, rfl⟩
    · exact h.keep rfl (Int.le_refl _)
    · exact stOk_respondAll h fun q hq => by rw [List.mem_singleton.mp hq]; exact Int.le_refl _
    · exact h.keep rfl (Int.le_refl _)
  · split at hR
    · subst hR; exact h.keep rfl (Int.le_refl _)
    · subst hR; exact h.keep rfl (Int.le_refl _)

/-- The deferred reads' release: answered at the commit index, or queued. -/
theorem stOk_release {c : CfgM} {id : w64} {X s2 : PState} (h : StOk X) (hR : ReleaseEnd c id X s2) :
    StOk s2 := by
  rcases hR with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · exact h.keep rfl (Int.le_refl _)
  · refine stOk_respondAll (s := { X with rd := { X.rd with pend := [] } })
      (h.keep rfl (Int.le_refl _)) fun q hq => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hq
    exact Int.le_refl _

/-- A leader's read acknowledgement: the confirmed requests were queued, at most the commit
(`ReadOk`). -/
theorem stOk_readAck {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : StOk s) (hro : ReadOk s)
    (hl : s.role = .leader) (hR : ReadAckEnd c id s m s') : StOk s' := by
  rcases hR with ⟨-, rfl⟩ | ⟨N', -, rfl⟩
  · exact h.keep rfl (Int.le_refl _)
  · refine stOk_respondAll (h.keep rfl (Int.le_refl _)) fun q hq => ?_
    have h1 := readonlyAdvance_out _ N' q hq
    rw [readonlyRecvAck_pending] at h1
    exact (hro.2 hl q h1).1

/-- The type switch keeps `StOk` (as `readOk_handle`). -/
theorem stOk_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : StOk s) (hro : ReadOk s)
    (hsc : RdTy m.ty) (hm : m.ty = .readIndexResp → uint.Z m.index < 2 ^ 61)
    (hh : HandleEnd kk c id s m s') : StOk s' := by
  have hc := commit_handle hsc hh
  unfold HandleEnd at hh
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at hh; simp only at hh; exact stOk_readIdx h hh
  · rw [hty] at hh; simp only at hh
    split at hh
    · rcases hh with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · intro st hst
        simp only [List.mem_append, List.mem_singleton] at hst
        rcases hst with hst | rfl
        · exact h st hst
        · exact .inr (hm hty)
      · exact h
      · exact h
    · subst hh; exact h
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;>
    simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h.keep rfl hc
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact h.keep rfl hc
      · obtain ⟨mt, ms, -, -, rfl⟩ := hw; exact h.keep rfl hc
      · exact h.keep rfl hc
    · subst hh; exact h.keep rfl hc
  · split at hh
    · subst hh; exact h.keep rfl hc
    · rcases hh with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩ <;>
        exact h.keep rfl hc
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, hn, hs'⟩ | ⟨-, x, n, s2, -, hn, hrel, hs'⟩
      · exact h.keep rfl hc
      · obtain ⟨ms, -, rfl⟩ := hs'; exact h.keep rfl hc
      · obtain ⟨ms, -, rfl⟩ := hs'; exact h.keep rfl hc
      · obtain ⟨ms, -, rfl⟩ := hs'
        exact (stOk_release (h.keep (t := { s with matched := _, commit := n }) rfl (Int.le_of_lt hn.1))
          hrel).keep rfl (Int.le_refl _)
    · subst hh; exact h.keep rfl hc
  · split at hh
    · subst hh; exact h.keep rfl hc
    · subst hh; exact h.keep rfl hc
  · split at hh
    · rename_i hr
      obtain ⟨s2, hs', ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := hh
      · obtain ⟨ms, -, rfl⟩ := hs'; exact h.keep rfl hc
      · obtain ⟨ms, -, rfl⟩ := hs'
        exact stOk_readAck (s := psendMsgs s ms) (h.keep rfl (Int.le_refl _)) hro hr ha
    · subst hh; exact h.keep rfl hc
  · unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact h.keep rfl hc
    · split at hh
      · subst hh; exact h.keep rfl hc
      · subst hh; exact h.keep rfl hc

theorem stOk_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : StOk s) (hro : ReadOk s)
    (hsc : RdTy m.ty) (hm : m.ty = .readIndexResp → uint.Z m.index < 2 ^ 61)
    (hr : RecvEnd kk c id s m s') : StOk s' := by
  have hc := commit_recv hsc hr
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact stOk_handle h hro hsc hm hh
  · exact h.keep rfl hc
  · exact h.keep rfl hc
  · exact h.keep rfl hc
  · exact h.keep rfl hc
  · have h1 : StOk s1 ∧ ReadOk s1 := by
      rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact ⟨h.keep rfl (Int.le_refl _), hro.nl rfl (by simp [pbecomeFollower])⟩
      · exact ⟨h.keep rfl (Int.le_refl _), hro⟩
      · exact ⟨h.keep rfl (Int.le_refl _), hro⟩
    exact stOk_handle h1.1 h1.2 hsc hm hh

theorem stOk_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (h : StOk s) (hro : ReadOk s)
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (ha : AdvanceEnd kk c id s qs s') :
    StOk s' := by
  induction ha with
  | nil => exact h
  | cons s s1 s' q qs hr _ ih =>
    have hty := hq q (List.mem_cons_self ..)
    have hsc : RdTy q.ty := by rcases hty with h' | h' <;> simp [RdTy, S4Ty, h']
    have hm : q.ty = .readIndexResp → uint.Z q.index < 2 ^ 61 := fun h' => by
      rcases hty with h'' | h'' <;> rw [h''] at h' <;> cases h'
    have hm' : q.ty = .readIndex → EntNums (2 ^ 61) q.entries := fun h' => by
      rcases hty with h'' | h'' <;> rw [h''] at h' <;> cases h'
    exact ih (stOk_recv h hro hsc hm hr) (readOk_recv hro hsc hm' hr)
      (fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- **`StOk` along `ReachP`**: a read state enters by a local answer, at an index at most the
commit, or by a received `MsgReadIndexResp`, at its index (`hrn`); commits only grow. -/
theorem stOk_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView}
    {ps₁ : PState} (h : StOk v.ps) (hro : ReadOk v.ps)
    (hrn : ∀ m ∈ net, m.ty = .readIndexResp → MsgNums (2 ^ 61) m)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .appResp ∨ q.ty = .voteResp)
    (hr : ReachP kk c id net xnet v ps₁) : StOk ps₁ := by
  have hc := commit_reachP hqs hr
  cases hr with
  | stay _ => exact h
  | recv m _ _ _ _ hmn _ _ hty hO => exact stOk_recv h hro hty (fun ht => (hrn m hmn ht).1) hO
  | recvP m _ _ _ _ _ _ _ hpt _ hP =>
    rcases recvEnd_pre hpt hP with rfl | ⟨-, -, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ |
        ⟨-, -, -, -, hcs⟩
    · exact h
    · exact h.keep rfl hc
    · exact h.keep rfl hc
    · exact h.keep rfl hc
    · exact h.keep rfl hc
    · obtain ⟨peers, -, rfl⟩ := hcs; exact h.keep rfl hc
  | tick _ _ _ ht =>
    rcases ht with rfl | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h
    all_goals exact h.keep rfl hc
  | propose d _ _ _ hh =>
    unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩
      · exact h
      · exact h.keep rfl hc
    · split at hh
      · subst hh; exact h.keep rfl hc
      · subst hh; exact h.keep rfl hc
  | read d _ _ _ hh => exact stOk_readIdx h hh
  | advance _ _ _ _ hno ha => exact stOk_adv h hro (fun q hq => hqs q hq (hno q hq)) ha
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact h
    · obtain ⟨peers, -, rfl⟩ := hcs; exact h.keep rfl hc
  | sends _ _ _ _ hs => obtain ⟨ms, -, rfl⟩ := hs; exact h.keep rfl hc
  | adoptX x _ _ _ _ _ _ => exact h.keep rfl hc
  | campX x p1 _ _ _ _ _ _ _ hp1 _ hce =>
    obtain ⟨-, peers, -, rfl⟩ := hce
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h.keep rfl hc

/-- **A reached state's read states have indices within `2 ^ 61`** (`readyReadIdx.law`, with its
premises): the view has none (`NodeFacts.states0`); along `ReachP` each is at most the commit then,
which only grows, or a `MsgReadIndexResp`'s index (`NetOk`); the commit reached is within `2 ^ 61`
(`StateNums`). -/
theorem readStates_reach {msk : SimMask} (_ : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} :
    InMask msk R net xnet → NetOk R S net → NodeOk R dec S net n v →
    ReachIn msk R dec Adm net xnet n v r₁ → StateNums (2 ^ 61) r₁.p →
    ∀ st ∈ r₁.p.rd.states, uint.Z st.Index' < 2 ^ 61 := by
  intro hin hnet hv hr hs
  have h0 : StOk v.ps := fun st hst => by rw [hv.facts.states0] at hst; cases hst
  have hk := stOk_reachP h0 hv.facts.readOk (fun m hmn => hnet.2.2.2.2.2.2 m hmn)
    (fun q hq hne => ((hv.qs q hq).self hne).2.2.2.2) (ReachIn.toP ‹_› hin hnet hv hr)
  intro st hst
  rcases hk st hst with h1 | h1
  · exact Int.lt_of_le_of_lt h1 hs.2.2.2.1
  · exact h1

end readstates

end AntSim
end EtcdGrove
end Perennial
