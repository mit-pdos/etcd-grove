/-
Lean-first (no Rocq counterpart). #33 S3b W4b (2026-11-23): the budget law of `OnDisk`
(`State.onDisk_within`), over `OnDiskLaws2`'s sections of `State.onDisk`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws2

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck
namespace OnDiskLaws2

set_option linter.unusedSimpArgs false

variable {x : OnDisk} {b E : Nat}

/-- `pre` within the budget before it is merged (`u7`): its facts at most two, its votes and acks at
most one, and the log it restores, `SubSeq(L0, 1, keep) \o suffix`, within `b`. -/
def PreOk (b E : Nat) (p : Pre) : Prop :=
  bigOk p.term ∧ bigOk p.voteTerm ∧ bigOk p.commit ∧ bigOk p.keep ∧ bigOk p.confirmed.term ∧
  bigOk p.confirmed.index ∧ bigOk p.low ∧ logWithin b E p.suffix ∧ 0 ≤ p.keep ∧
  p.keep + p.suffix.length ≤ b ∧ p.msgs.length ≤ 2 ∧ (∀ f ∈ p.msgs, f.NumsOk) ∧ p.acks.length ≤ 1 ∧
  (∀ f ∈ p.acks, f.NumsOk) ∧ p.votes.length ≤ 1 ∧ (∀ v ∈ p.votes, bigOk v.term)

/-- `pre` with its kept prefix (`u4`). -/
def setKS (p : Pre) (k : Int) (suf : List Entry) : Pre := { p with keep := k, suffix := suf }

theorem PreOk.acks {p : Pre} {a : Fact} (h : PreOk b E p) (ha : a.NumsOk) : PreOk b E { p with acks := [a] } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, by simp, by simpa using ha, h15, h16⟩

theorem PreOk.low {p : Pre} {l : Int} (h : PreOk b E p) (hl : bigOk l) : PreOk b E { p with low := l } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, hl, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem PreOk.within {p : Pre} (h : PreOk b E p) : p.Within (b + 1) E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8.mono' (by omega) (Nat.le_refl _), by omega, by omega, h12,
    by omega, h14, by omega, h16⟩

theorem Pre.Within.empty : ({} : Pre).Within b E :=
  ⟨bigOk_zero, bigOk_zero, bigOk_zero, bigOk_zero, bigOk_zero, bigOk_zero, bigOk_zero,
    ⟨by simp, by simp⟩, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem imin_bigOk {a c : Int} (ha : bigOk a) (hc : bigOk c) : bigOk (imin a c) := by
  unfold imin; split <;> assumption

theorem lowest_bigOk {a c : Int} (ha : bigOk a) (hc : bigOk c) : bigOk (lowest a c) := by
  unfold lowest; split
  · exact hc
  · split
    · exact ha
    · exact imin_bigOk ha hc

/-- The merged write within the budget. -/
theorem nuOf_within {u p : Pre} {suf : List Entry} (hu : u.Within b E) (hp : PreOk b E p)
    (hs : logWithin b E suf) (hk : imin u.keep p.keep + suf.length ≤ b) :
    (nuOf u p suf).Within (b + 1) E := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15⟩ := hu
  obtain ⟨-, -, -, p4, -, -, p7, -, -, -, p11, p12, p13, p14, p15, p16⟩ := hp
  unfold nuOf
  refine ⟨u1, u2, u3, imin_bigOk u4 p4, u5, u6, lowest_bigOk u7 p7, hs.mono' (by omega) (Nat.le_refl _),
    by simp only; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := lset_union_len u.msgs p.msgs; simp only; omega
  · intro f hf; rcases lset_union_mem hf with hf | hf
    · exact u11 f hf
    · exact p12 f hf
  · have := lset_union_len u.acks p.acks; simp only; omega
  · intro f hf; rcases lset_union_mem hf with hf | hf
    · exact u13 f hf
    · exact p14 f hf
  · have := lset_union_len u.votes p.votes; simp only; omega
  · intro v hv; rcases lset_union_mem hv with hv | hv
    · exact u15 v hv
    · exact p16 v hv

theorem undo_within (hW : x.Within b E) : ((x.s.undo[x.n]!).getD {}).Within b E := by
  cases hu : x.s.undo[x.n]! with
  | none => exact Pre.Within.empty
  | some u => exact hW.1.undo (some u) (getElem!_some_mem hu) u rfl

/-- The successor within `b + 1`, from the sections. -/
theorem within_of {s' : State} (hW : x.Within b E) (hb : ((b + 1 : Nat) : Int) < numBound)
    (ho : g1 x (g2 x (g3 x (g4 x (g5 x (g6 x (succ x)))))) = .ok (some s')) (hv : s'.viol = []) :
    s'.Within (b + 1) E := by
  obtain ⟨h, hS⟩ := chain_some ho
  unfold succ at h
  obtain ⟨t1, voted, vf, hT1, -, h⟩ := u0_ok h
  obtain ⟨L1, c, c1, el, hL1, hc, hc1, -, h⟩ := u1_ok h
  obtain ⟨msgs', h, hmsgs⟩ := u2_ok h
  obtain ⟨votes', h, hvotes⟩ := u3_ok h
  obtain ⟨pre1, h, hpre1⟩ := u4_ok h
  obtain ⟨pre2, h, hpre2⟩ := u5_ok h
  obtain ⟨pre3, h, hpre3⟩ := u6_ok h
  obtain ⟨p, h, hp⟩ := u7_ok h
  obtain ⟨ch1, tl', hch1, h, htl'⟩ := u8_ok h
  have hs' := u9_some h
  have hb' := hb
  unfold numBound at hb'
  have hWs := hW.1
  have hWs1 : x.s.Within (b + 1) E := hWs.mono' (by omega) (Nat.le_refl _)
  have ht1 := T1_bigOk hW hT1
  -- the facts
  have hm1n : ∀ f ∈ (if el then lset.add x.s.msgs (x.s.voteRequest x.n t1) else x.s.msgs), f.NumsOk := by
    intro f hf
    cases el
    · exact hWs.msgs f hf
    · rcases lset_add_mem hf with hf | hf
      · exact hWs.msgs f hf
      · subst hf; exact voteRequest_nums hW hb ht1
  have hm1l : (if el then lset.add x.s.msgs (x.s.voteRequest x.n t1) else x.s.msgs).length ≤ x.s.msgs.length + 1 ∧
      (lset.minus (if el then lset.add x.s.msgs (x.s.voteRequest x.n t1) else x.s.msgs) x.s.msgs).length ≤ 1 := by
    cases el
    · simp [lset_minus_self]
    · have := lset_add_len x.s.msgs (x.s.voteRequest x.n t1)
      have := lset_minus_add x.s.msgs x.s.msgs (x.s.voteRequest x.n t1)
      simp only [ite_true, lset_minus_self, List.length_nil] at *
      omega
  have hmn : ∀ f ∈ msgs', f.NumsOk := by
    rcases hmsgs with ⟨-, rfl⟩ | ⟨f, a, -, hf, ha, rfl⟩
    · exact hm1n
    · intro g hg
      rcases lset_add_mem hg with hg | hg
      · exact hm1n g hg
      · subst hg; exact ackFact_nums ht1 (ackAt_bigOk hW hb hS ha)
  have hml : msgs'.length ≤ x.s.msgs.length + 2 ∧ (lset.minus msgs' x.s.msgs).length ≤ 2 := by
    rcases hmsgs with ⟨-, rfl⟩ | ⟨f, a, -, hf, ha, rfl⟩
    · omega
    · have := lset_add_len (if el then lset.add x.s.msgs (x.s.voteRequest x.n t1) else x.s.msgs)
        (ackFact (x.s.cfg.server[x.n]!) f.src t1 a)
      have := lset_minus_add (if el then lset.add x.s.msgs (x.s.voteRequest x.n t1) else x.s.msgs) x.s.msgs
        (ackFact (x.s.cfg.server[x.n]!) f.src t1 a)
      omega
  -- the votes
  have hvn : ∀ v ∈ votes', bigOk v.term := by
    rcases hvotes with ⟨-, rfl⟩ | ⟨v, -, rfl⟩
    · exact hWs.votes
    · intro w hw
      rcases lset_add_mem hw with hw | hw
      · exact hWs.votes w hw
      · subst hw; exact ht1
  have hvl : votes'.length ≤ x.s.votes.length + 1 ∧ (lset.minus votes' x.s.votes).length ≤ 1 := by
    rcases hvotes with ⟨-, rfl⟩ | ⟨v, -, rfl⟩
    · simp [lset_minus_self]
    · have := lset_add_len x.s.votes { voter := x.s.cfg.server[x.n]!, term := t1, cand := v }
      have := lset_minus_add x.s.votes x.s.votes { voter := x.s.cfg.server[x.n]!, term := t1, cand := v }
      rw [lset_minus_self] at this
      simp only [List.length_nil] at this
      omega
  -- `pre`
  have hL0 := L0_within hW
  have hP1 : PreOk b E pre1 := by
    have h0 : ∀ (ns : State) (k : Int) (suf : List Entry), ns.msgs = msgs' → ns.votes = votes' → bigOk k →
        0 ≤ k → logWithin b E suf → k + suf.length ≤ b → PreOk b E (setKS (pre0 x ns) k suf) := by
      intro ns k suf hm hvt hk hk0 hsuf hks
      unfold setKS pre0
      rw [hm, hvt]
      refine ⟨getElem!_bigOk hWs.currentTerm, getElem!_bigOk hWs.voteTerm, getElem!_bigOk hWs.commitIndex,
        hk, (getElem!_mem' (n := x.n) hWs.confirmed ⟨bigOk_zero, bigOk_zero⟩).1,
        (getElem!_mem' (n := x.n) hWs.confirmed ⟨bigOk_zero, bigOk_zero⟩).2, bigOk_zero, hsuf, hk0, hks,
        hml.2, fun f hf => hmn f (lset_minus_mem hf), by simp, by simp, hvl.2,
        fun v hv => hvn v (lset_minus_mem hv)⟩
    rcases hpre1 with ⟨-, rfl⟩ | ⟨fi, suf, hst, hfi, hsuf, rfl⟩
    · have := hL0.1
      exact h0 _ _ [] rfl rfl (by unfold bigOk; omega) (by omega) ⟨by simp, by simp⟩ (by simp; omega)
    · have hfb := first_bigOk hW hb hfi
      obtain ⟨fi', es, q', hq', hfi', hes, hlen⟩ := hS hst
      rw [hfi] at hfi'; cases hfi'
      have hqb := (ll_within hW hq').2.1
      have hsl : (suf.length : Int) ≤ x.L0.length := by have := subSeq_length_le hsuf; omega
      have hsw : logWithin b E suf := ⟨by have := hL0.1; omega, fun e he => hL0.2 e (subSeq_mem hsuf he)⟩
      by_cases hc : fi > x.L0.length
      · unfold subSeq at hsuf
        rw [if_pos hc] at hsuf
        cases hsuf
        exact h0 _ _ [] rfl rfl hfb.2 (by omega) ⟨by simp, by simp⟩ (by simp; omega)
      · have hfi1 : 1 ≤ fi := by
          unfold subSeq at hsuf
          rw [if_neg hc] at hsuf
          split at hsuf
          · cases hsuf
          · omega
        have := subSeq_len_eq hfi1 (by omega) hsuf
        have := hL0.1
        exact h0 _ _ suf rfl rfl hfb.2 (by omega) hsw (by omega)
  have hP2 : PreOk b E pre2 := by
    rcases hpre2 with ⟨-, rfl⟩ | ⟨f, a, -, hf, ha, rfl⟩
    · exact hP1
    · exact hP1.acks (ackFact_nums ht1 (ackAt_bigOk hW hb hS ha))
  have hP3 : PreOk b E pre3 := by
    rcases hpre3 with ⟨-, rfl⟩ | ⟨fi, -, hfi, rfl⟩
    · exact hP2
    · exact hP2.low (first_bigOk hW hb hfi).1
  have hpW : p.Within (b + 1) E := by
    rcases hp with ⟨-, rfl⟩ | ⟨suf, -, rfl, hsuf⟩
    · exact hP3.within
    · have hu := undo_within hW
      rcases hsuf with ⟨hk, rfl⟩ | ⟨hk, l, hl, rfl⟩
      · refine nuOf_within hu hP3 hu.2.2.2.2.2.2.2.1 ?_
        have := hu.2.2.2.2.2.2.2.2.1
        unfold imin; rw [if_pos (by omega)]; omega
      · have hk0 := hP3.2.2.2.2.2.2.2.2.1
        have hll := subSeq_len_eq (by omega) (by omega) hl
        have huk := hu.2.2.2.2.2.2.2.2.1
        have hus := hu.2.2.2.2.2.2.2.1
        refine nuOf_within hu hP3 ⟨?_, fun e he => ?_⟩ ?_
        · simp only [List.length_append]; omega
        · rcases List.mem_append.1 he with he | he
          · exact hL0.2 e (subSeq_mem hl he)
          · exact hus.2 e he
        · unfold imin; rw [if_neg (by omega)]; simp only [List.length_append]; omega
  -- the successor
  rw [hs']
  refine State.Within.intro hWs1.cfg hWs1.i_pos hWs1.i_le (forall_mem_set hWs1.currentTerm ht1) ?_
    (forall_mem_set hWs1.commitIndex (commit_bigOk hW hc)) hWs1.lastApplied hWs1.confAt
    (forall_mem_set hWs1.confirmed (conf1_bigOk hW hb hS hc1))
    (forall_mem_set hWs1.log ((L1_within hW hS hL1).mono' (by omega) (Nat.le_refl _)))
    ((ch1_within hW hS hch1).mono' (by omega) (Nat.le_refl _)) ?_ ?_ hWs1.config hWs1.ledConf_len
    hWs1.ledConf hWs1.ledAt hWs1.elAt ?_ ?_ hmn ?_ hvn ?_ hW.2.2.2.2.2.1 ?_ hWs1.pending hWs1.queue
    hWs1.reads ?_
  · show ∀ y ∈ (ns0 x t1 voted vf).voteTerm, bigOk y
    unfold ns0
    cases voted
    · exact hWs1.voteTerm
    · exact forall_mem_set hWs1.voteTerm ht1
  · show x.ll.length ≤ b + 1
    have := hW.2.2.2.2.2.2.1; omega
  · exact fun q hq => ⟨(ll_within hW hq).1, (ll_within hW hq).2.mono' (by omega) (Nat.le_refl _)⟩
  · rcases htl' with ⟨-, rfl⟩ | ⟨o, nc, -, ho, hnc, rfl⟩
    · exact hW.2.2.2.2.2.2.2.2.2.1.mono' (by omega)
    · refine termIntsWithin_with hW.2.2.2.2.2.2.2.2.2.1 ht1 (imax_bigOk (old_bigOk hW ho) ?_)
      have := (newC_within hW hS hnc).1
      unfold bigOk; omega
  · show msgs'.length ≤ 2 * (b + 1)
    have := hWs.msgs_len; have := hml.1; omega
  · show votes'.length ≤ b + 1
    have := hWs.votes_len; have := hvl.1; omega
  · show x.ld.length ≤ b + 1
    have := hW.2.2.2.2.1; omega
  · exact forall_mem_set hWs1.undo (fun u hu => by cases hu; exact hpW)
  · show s'.viol.length ≤ b + 1
    rw [hv]; simp

end OnDiskLaws2

/-- **`OnDisk`'s successor within budget** (W4b). -/
theorem State.onDisk_within : OnDiskWithin := by
  intro s n q more ro ld ll ch tl vi b E s' _ hW hb ho hv
  rw [OnDiskLaws2.onDisk_eq] at ho
  exact OnDiskLaws2.within_of hW hb ho hv

end AntCheck
end EtcdGrove
end Perennial
