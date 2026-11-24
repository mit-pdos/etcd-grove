/-
Lean-first (no Rocq counterpart). #33 S3b W3b (2026-11-23): the budget law of `InMemory`
(`State.inMemory_within`): its result within `b + ev.size + 1`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.InMemLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem lset_add_length_le {α : Type} [DecidableEq α] (s : List α) (x : α) :
    (lset.add s x).length ≤ s.length + 1 := by
  unfold lset.add; split <;> simp

theorem lset_mem_add {α : Type} [DecidableEq α] {s : List α} {x y : α} (h : y ∈ lset.add s x) :
    y = x ∨ y ∈ s := by
  unfold lset.add at h; split at h
  · exact .inr h
  · rcases List.mem_append.1 h with h | h
    · exact .inr h
    · exact .inl (List.mem_singleton.1 h)

/-- `SubSeq(l, m, n)`: a piece of `l`, so within `l`'s budget. -/
theorem subSeq_within {B E : Nat} {l r : List Entry} {m n : Int} (hl : logWithin B E l)
    (h : subSeq l m n = .ok r) : logWithin B E r := by
  unfold subSeq at h
  split at h
  · cases h; exact logWithin_nil _ _
  split at h
  · cases h
  cases h
  refine ⟨?_, fun e he => hl.2 e (List.mem_of_mem_drop (List.mem_of_mem_take he))⟩
  have := hl.1
  simp only [List.length_take, List.length_drop]
  omega

/-- An invariant of a `foldlM` in `EvalM`. -/
theorem foldlM_ok_inv {α β : Type} (P : α → Prop) {f : α → β → EvalM α} {xs : List β} {a r : α}
    (h0 : P a) (hs : ∀ a b a', P a → f a b = .ok a' → P a') (h : xs.foldlM f a = .ok r) : P r := by
  induction xs generalizing a with
  | nil => cases h; exact h0
  | cons y t ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨a', ha', h⟩ := bind_ok h
    exact ih (hs a y a' h0 ha') h

/-- An invariant of a `foldlM` over `0..k-1` in `EvalM`, indexed by the count done. -/
theorem foldlM_range_ok_inv {α : Type} (P : Nat → α → Prop) {f : α → Nat → EvalM α} {a r : α} {k : Nat}
    (h0 : P 0 a) (hs : ∀ i a a', P i a → f a i = .ok a' → P (i + 1) a')
    (h : (List.range k).foldlM f a = .ok r) : P k r := by
  induction k generalizing r with
  | zero => cases h; exact h0
  | succ k ih =>
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨c1, hc1, h⟩ := bind_ok h
    simp only [List.foldlM_cons, List.foldlM_nil] at h
    obtain ⟨c2, h, h'⟩ := bind_ok h
    cases h'
    exact hs k c1 r (ih hc1) h

theorem atE_index {l : List Entry} {k : Int} {e : Entry} (h : atE l k = .ok e) : 1 ≤ k ∧ k ≤ l.length := by
  unfold atE at h; split at h
  · cases h
  · rename_i hk; omega

/-- `LastConf(l, a)`: 0 or an index of `l`. -/
theorem lastConf_bounds {l : List Entry} {a k : Int} (h : lastConf l a = .ok k) :
    0 ≤ k ∧ k ≤ l.length := by
  unfold lastConf at h
  refine foldlM_ok_inv (fun k : Int => 0 ≤ k ∧ k ≤ l.length) (by simp) ?_ h
  intro acc i acc' hacc hs
  obtain ⟨e, he, hs⟩ := bind_ok hs
  have hi := atE_index he
  simp only [pure_ok, Except.ok.injEq] at hs
  subst hs
  split <;> omega

theorem take_chgSum_succ {l : List Entry} {k : Nat} (hk : k < l.length) :
    ((l.take (k + 1)).map Entry.chgSize).sum = ((l.take k).map Entry.chgSize).sum + (l[k]).chgSize := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

theorem take_chgSum_le (l : List Entry) (k : Nat) :
    ((l.take k).map Entry.chgSize).sum ≤ (l.map Entry.chgSize).sum := by
  conv => rhs; rw [← List.take_append_drop k l]
  rw [List.map_append, List.sum_append]
  omega

/-- `ConfOf(l, a, c0)`: each set at most `c0`'s first set plus the changes of `l`. -/
theorem confOf_length {l : List Entry} {a : Int} {c0 c : Conf} (h : confOf l a c0 = .ok c)
    (h0 : c0.cout.length ≤ c0.cin.length) :
    c.cin.length ≤ c0.cin.length + (l.map Entry.chgSize).sum ∧
    c.cout.length ≤ c0.cin.length + (l.map Entry.chgSize).sum := by
  unfold confOf at h
  split at h
  · cases h
  dsimp only at h
  have H := foldlM_range_ok_inv (fun k (c : Conf) =>
      c.cin.length ≤ c0.cin.length + ((l.take k).map Entry.chgSize).sum ∧
      c.cout.length ≤ c0.cin.length + ((l.take k).map Entry.chgSize).sum)
    (by simp; omega) ?_ h
  · have := take_chgSum_le l a.toNat
    exact ⟨by omega, by omega⟩
  intro k c1 c2 ⟨i1, i2⟩ h
  obtain ⟨e, he, h⟩ := bind_ok h
  have hk : k < l.length := by have := atE_index he; omega
  have hek : e = l[k] := by
    unfold atE at he; split at he
    · cases he
    · cases he
      rw [List.getElem!_eq_getElem?_getD, show ((k : Int) + 1 - 1).toNat = k by omega,
        List.getElem?_eq_getElem hk]
      rfl
  subst hek
  rw [take_chgSum_succ hk]
  split at h
  · have := nextConf_length h
    unfold Entry.chgSize at *
    exact ⟨by omega, by omega⟩
  · cases h; exact ⟨by omega, by omega⟩

namespace InMem
variable {x : InMem} {b E : Nat}

theorem c_bigOk (hN : x.ev.NumsOk) {c : Int} (h : x.c = .ok c) : bigOk c := by
  unfold InMem.c at h
  have h1 := hN.2.1
  rw [need_ok h] at h1
  exact bigOk_of_numOk h1

theorem ld1_within (hW : x.s.Within b E) (hN : x.ev.NumsOk) {l : List LeaderRec} (h : x.ld1 = .ok l) :
    l.length ≤ b + 1 ∧ ∀ r ∈ l, bigOk r.term := by
  unfold InMem.ld1 at h
  obtain ⟨w, -, h⟩ := bind_ok h
  cases w
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at h
    subst h
    exact ⟨by have := hW.leaders_len; omega, hW.leaders⟩
  · simp only [ite_true] at h
    obtain ⟨t, ht, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    refine ⟨(by have := lset_add_length_le x.s.leaders { server := x.s.cfg.server[x.n]!, term := t }
                have := hW.leaders_len; omega), fun r hr => ?_⟩
    rcases lset_mem_add hr with h' | h'
    · subst h'; exact T_bigOk hN ht
    · exact hW.leaders r h'

theorem lc1_bounds (hW : x.s.Within b E) (hN : x.ev.NumsOk) {l : TermFn Conf} (h : x.lc1 = .ok l) :
    l.length ≤ b + 1 ∧ ∀ q ∈ l, bigOk q.1 ∧ confWithin x.s.cfg.initVoters.length b E q.2 := by
  unfold InMem.lc1 at h
  obtain ⟨w, -, h⟩ := bind_ok h
  cases w
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at h
    subst h
    exact ⟨by have := hW.ledConf_len; omega, hW.ledConf⟩
  · simp only [ite_true] at h
    obtain ⟨t, ht, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    refine ⟨by have := TermFn.with_length_le x.s.ledConf t (x.s.config[x.n]!); have := hW.ledConf_len; omega,
      fun q hq => ?_⟩
    rcases TermFn.mem_with hq with h' | h'
    · subst h'
      exact ⟨T_bigOk hN ht, getElem!_mem' (α := Conf) (P := fun c => confWithin _ b E c) hW.config
        ⟨Nat.zero_le _, Nat.zero_le _⟩⟩
    · exact hW.ledConf q h'

/-- `newC`: a piece of `L`. -/
theorem newC_within (hW : x.s.Within b E) (hN : x.ev.NumsOk) (hC : x.ev.ChgOk E) {l : List Entry}
    (h : x.newC = .ok l) : logWithin (b + x.ev.size) E l := by
  unfold InMem.newC at h
  obtain ⟨L, hL, h⟩ := bind_ok h
  obtain ⟨c, -, h⟩ := bind_ok h
  exact subSeq_within (L_within hW hN hC hL) h

end InMem

theorem State.inMemory_within : InMemoryWithin := by
  intro s n ev b E r hn hW hN hC hb h
  unfold State.inMemory at h
  replace h := bind_ok h; obtain ⟨ok, -, h⟩ := h
  replace h := bind_ok h; obtain ⟨r1, -, h⟩ := h
  replace h := bind_ok h; obtain ⟨ld, hld, h⟩ := h
  replace h := bind_ok h; obtain ⟨l2, hl2, h⟩ := h
  replace h := bind_ok h; obtain ⟨lc, hlc, h⟩ := h
  extract_lets viol0 lc0 me vCS jp1 at h
  have : ∃ cc : List Conf × List Int, (∀ c ∈ cc.1, confWithin s.cfg.initVoters.length b E c) ∧
      (∀ a ∈ cc.2, bigOk a) ∧ jp1 cc = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨sn, hsn, h⟩ := h
      replace h := bind_ok h; obtain ⟨c, hc, h⟩ := h
      replace h := bind_ok h; obtain ⟨sn', hsn', h⟩ := h
      replace h := bind_ok h; obtain ⟨a, ha, h⟩ := h
      replace h := bind_ok h; obtain ⟨cc, hcc, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hcc
      subst hcc
      refine ⟨(s.config.set n c, s.confAt.set n a), ?_, ?_, h⟩
      · have hcl := confOf_length hc (by simp [State.initConf, Config.initConf])
        have hs := logWithin_chgSum hW.chain
        simp only [State.initConf, Config.initConf] at hcl
        exact forall_mem_set hW.config ⟨by omega, by omega⟩
      · have hal := lastConf_bounds ha
        have := hW.chain.1
        unfold numBound at hb
        exact forall_mem_set hW.confAt ⟨by omega, by omega⟩
    · replace h := bind_ok h; obtain ⟨cc, hcc, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hcc
      subst hcc
      exact ⟨(s.config, s.confAt), hW.config, hW.confAt, h⟩
  obtain ⟨⟨config, confAt⟩, hcf, hca, h⟩ := this
  simp -zeta only [jp1] at h
  replace h := bind_ok h; obtain ⟨w, hw, h⟩ := h
  extract_lets jp2 at h
  have : ∃ p : TermFn Int × TermFn Int, termIntsWithin (b + 1) p.1 ∧ termIntsWithin (b + 1) p.2 ∧
      jp2 p = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨t, ht, h⟩ := h
      replace h := bind_ok h; obtain ⟨t', ht', h⟩ := h
      replace h := bind_ok h; obtain ⟨p, hp, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hp
      subst hp
      have hca : bigOk (s.confAt[n]!) := getElem!_mem' (α := Int) (P := bigOk) hW.confAt ⟨by decide, by decide⟩
      exact ⟨(s.ledAt.with t s.confAt[n]!, s.elAt.with t' s.confAt[n]!),
        termIntsWithin_with hW.ledAt (InMem.T_bigOk hN ht) hca,
        termIntsWithin_with hW.elAt (InMem.T_bigOk hN ht') hca, h⟩
    · replace h := bind_ok h; obtain ⟨p, hp, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hp
      subst hp
      exact ⟨(s.ledAt, s.elAt), hW.ledAt.mono' (by omega), hW.elAt.mono' (by omega), h⟩
  obtain ⟨⟨ledAt, elAt⟩, hla, hea, h⟩ := this
  simp -zeta only [jp2] at h
  replace h := bind_ok h; obtain ⟨cd, -, h⟩ := h
  extract_lets jp3 at h
  have : ∃ ch : List Entry, logWithin (b + ev.size) E ch ∧ jp3 ch = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨ch, hch, h⟩ := h
      refine ⟨ch, ?_, h⟩
      exact InMem.newC_within (x := { s := s, n := n, ev := ev }) hW hN hC hch
    · replace h := bind_ok h; obtain ⟨ch, hch, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hch
      subst hch
      exact ⟨s.chain, hW.chain.mono' (by omega) (Nat.le_refl _), h⟩
  obtain ⟨chain, hch, h⟩ := this
  simp -zeta only [jp3] at h
  replace h := bind_ok h; obtain ⟨cm, -, h⟩ := h
  extract_lets jp4 at h
  have : ∃ tl : TermFn Int, termIntsWithin (b + 1) tl ∧ jp4 tl = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨t, ht, h⟩ := h
      replace h := bind_ok h; obtain ⟨c, hc, h⟩ := h
      replace h := bind_ok h; obtain ⟨tl, htl, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at htl
      subst htl
      exact ⟨s.termLen.with t c, termIntsWithin_with hW.termLen (InMem.T_bigOk hN ht) (InMem.c_bigOk hN hc), h⟩
    · replace h := bind_ok h; obtain ⟨tl, htl, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at htl
      subst htl
      exact ⟨s.termLen, hW.termLen.mono' (by omega), h⟩
  obtain ⟨termLen, htl, h⟩ := this
  simp -zeta only [jp4] at h
  replace h := bind_ok h; obtain ⟨d1, -, h⟩ := h
  extract_lets jpF jpU jp5 at h
  have : ∃ v : SSet, v.length ≤ s.viol.length + 1 ∧ jp5 () v = .ok r := by
    split at h
    · exact ⟨vCS, setAdd_length_le _ _, h⟩
    · exact ⟨viol0, by simp [viol0], h⟩
  obtain ⟨v1, hv1, h⟩ := this
  simp -zeta only [jp5] at h
  replace h := bind_ok h; obtain ⟨d2, -, h⟩ := h
  extract_lets vLC jp7 jp6 at h
  have : ∃ l : Bool, jp6 () l = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨_, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨l, -, h⟩ := h
      exact ⟨l, h⟩
    · exact ⟨_, h⟩
  clear h
  obtain ⟨l1, h⟩ := this
  simp -zeta only [jp6] at h
  replace h := bind_ok h; obtain ⟨d3, -, h⟩ := h
  have : ∃ l : Bool, jp7 () l = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨l, -, h⟩ := h
      exact ⟨l, h⟩
    · exact ⟨_, h⟩
  clear h
  obtain ⟨l2', h⟩ := this
  simp -zeta only [jp7] at h
  have : ∃ v : SSet, v.length ≤ s.viol.length + 2 ∧ jpU () v = .ok r := by
    split at h
    · exact ⟨vLC, by have := setAdd_length_le v1 [76#8, 101#8, 97#8, 100#8, 101#8, 114#8, 67#8, 111#8, 109#8,
        112#8, 108#8, 101#8, 116#8, 101#8, 110#8, 101#8, 115#8, 115#8]; simp only [vLC]; omega, h⟩
    · exact ⟨v1, by omega, h⟩
  clear h
  obtain ⟨v2, hv2, h⟩ := this
  simp -zeta only [jpU] at h
  replace h := bind_ok h; obtain ⟨_, -, h⟩ := h
  have : ∃ v : SSet, v.length ≤ s.viol.length + 3 ∧ jpF () v = .ok r := by
    split at h
    · exact ⟨_, by have := setAdd_length_le v2 [85#8, 110#8, 112#8, 114#8, 111#8, 109#8, 111#8, 116#8, 97#8, 98#8,
        108#8, 101#8]; omega, h⟩
    · exact ⟨v2, by omega, h⟩
  clear h
  obtain ⟨v3, hv3, h⟩ := this
  simp -zeta only [jpF, pure_ok, Except.ok.injEq] at h
  subst h
  have hld' := InMem.ld1_within (x := { s := s, n := n, ev := ev }) hW hN hld
  have hl2' := InMem.ll2_within (x := { s := s, n := n, ev := ev }) hW hN hC hl2
  have hlc' := InMem.lc1_bounds (x := { s := s, n := n, ev := ev }) hW hN hlc
  dsimp only at hld' hl2' hlc'
  refine ⟨?_, hld'.2, ?_,
    fun p hp => ⟨(hl2'.2 p hp).1, (hl2'.2 p hp).2.mono' (by omega) (Nat.le_refl _)⟩, ?_,
    fun p hp => ⟨(hlc'.2 p hp).1, (hlc'.2 p hp).2.mono' (by omega) (Nat.le_refl _)⟩,
    fun c hc => (hcf c hc).mono' (by omega) (Nat.le_refl _), hca, hla.mono' (by omega), hea.mono' (by omega),
    htl.mono' (by omega), hch.mono' (by omega) (Nat.le_refl _), hv3⟩
  · exact Nat.le_trans hld'.1 (by omega)
  · exact hl2'.1
  · exact Nat.le_trans hlc'.1 (by omega)

end AntCheck
end EtcdGrove
end Perennial
