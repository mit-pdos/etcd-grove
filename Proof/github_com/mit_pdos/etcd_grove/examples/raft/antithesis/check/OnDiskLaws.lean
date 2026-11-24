/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): pure laws of `OnDisk`'s methods for
their proofs: the request `fm` and the message `m` within the budget (`OnDisk.Within`), so that the
Go's `int` arithmetic on them does not overflow.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem numOk_bigOk {x : Int} (h : numOk x) : bigOk x := by
  unfold numOk numBound at h; unfold bigOk; omega

theorem optNumOk_some {x : Int} (h : optNumOk (some x)) : numOk x := h

theorem msgSeqHead_mem {ms : List Msg} {m : Msg} (h : msgSeqHead ms = .ok m) : m ∈ ms := by
  cases ms with
  | nil => cases h
  | cons a l => cases h; exact List.mem_cons_self

theorem subSeq_length_le {l r : List Entry} {a c : Int} (h : subSeq l a c = .ok r) : r.length ≤ l.length := by
  unfold subSeq at h
  split at h
  · cases h; simp
  split at h
  · cases h
  cases h
  simp only [List.length_take, List.length_drop]; omega

theorem TermFn.get_mem {α : Type} {f : TermFn α} {t : Int} {v : α} (h : f.get t = .ok v) :
    ∃ p ∈ f, p.1 = t ∧ p.2 = v := by
  unfold TermFn.get at h
  split at h
  · rename_i p hp
    cases h
    obtain ⟨h1, h2⟩ := List.find?_eq_some_iff_append.1 hp
    exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using h1, rfl⟩
  · cases h

theorem OnDisk.Bounded.get {x : OnDisk} (h : x.Bounded) :
    ∃ b E : Nat, ((b + 1 : Nat) : Int) < numBound ∧ x.Within b E := h

theorem OnDisk.m_within {x : OnDisk} {b E : Nat} {m : Msg} (hW : x.Within b E) (hm : x.m = .ok m) :
    m.Within b E :=
  hW.2.2.2.1 m (msgSeqHead_mem hm)

/-- A request's (`ReqFactIn(ll, m)`'s) numbers and entries within the budget. -/
theorem reqFactIn_within {ll : TermFn (List Entry)} {m : Msg} {b E : Nat} {f : AppendFact} (hmw : m.NumsOk ∧ m.size ≤ b)
    (hll : ∀ p ∈ ll, bigOk p.1 ∧ logWithin b E p.2) (h : reqFactIn ll m = .ok f) :
    numOk f.prevLogIndex ∧ f.entries.length ≤ b ∧ numOk f.commit ∧ numOk f.term ∧ numOk f.prevLogTerm := by
  obtain ⟨⟨hnt, hni, hnl, hnc, hne⟩, hsz⟩ := hmw
  have hb0 : numOk 0 := by unfold numOk numBound; omega
  unfold reqFactIn at h
  obtain ⟨ty, hty, h⟩ := bind_ok h
  split at h
  · -- a snapshot: the leader log's prefix
    obtain ⟨t, ht, h⟩ := bind_ok h
    have htm := need_ok ht
    rw [htm] at hnt
    dsimp only at h
    split at h
    · obtain ⟨l, hl, h⟩ := bind_ok h
      obtain ⟨k', -, h⟩ := bind_ok h
      obtain ⟨es, hes, h⟩ := bind_ok h
      obtain ⟨p, hp, -, hp2⟩ := TermFn.get_mem hl
      have hpl := (hll p hp).2.1
      rw [hp2] at hpl
      obtain ⟨src, -, h⟩ := bind_ok h
      obtain ⟨dst, -, h⟩ := bind_ok h
      obtain ⟨t', ht', h⟩ := bind_ok h
      obtain ⟨k, hk, h⟩ := bind_ok h
      cases h
      rw [ht] at ht'; cases ht'
      have hkm := need_ok hk
      rw [hkm] at hni
      exact ⟨hb0, Nat.le_trans (subSeq_length_le hes) hpl, hni, hnt, hb0⟩
    · obtain ⟨es, hes, h⟩ := bind_ok h
      cases hes
      obtain ⟨src, -, h⟩ := bind_ok h
      obtain ⟨dst, -, h⟩ := bind_ok h
      obtain ⟨t', ht', h⟩ := bind_ok h
      obtain ⟨k, hk, h⟩ := bind_ok h
      cases h
      rw [ht] at ht'; cases ht'
      have hkm := need_ok hk
      rw [hkm] at hni
      exact ⟨hb0, Nat.zero_le _, hni, hnt, hb0⟩
  · -- `ToAppendFact(m)`
    unfold toAppendFact at h
    obtain ⟨src, -, h⟩ := bind_ok h
    obtain ⟨dst, -, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨p, hp, h⟩ := bind_ok h
    obtain ⟨pt, hpt, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    obtain ⟨c, hc, h⟩ := bind_ok h
    cases h
    have h1 := need_ok ht; have h2 := need_ok hp; have h3 := need_ok hpt; have h4 := need_ok hes
    have h5 := need_ok hc
    rw [h1] at hnt; rw [h2] at hni; rw [h3] at hnl; rw [h5] at hnc
    refine ⟨hni, ?_, hnc, hnt, hnl⟩
    unfold Msg.size at hsz; rw [h4] at hsz; simpa using hsz

/-- The request `fm`'s numbers and entries within the budget. -/
theorem OnDisk.fm_within {x : OnDisk} {b E : Nat} {f : AppendFact} (hW : x.Within b E) (h : x.fm = .ok f) :
    numOk f.prevLogIndex ∧ f.entries.length ≤ b ∧ numOk f.commit ∧ numOk f.term ∧ numOk f.prevLogTerm := by
  unfold OnDisk.fm at h
  obtain ⟨m, hm, h⟩ := bind_ok h
  have hmw := OnDisk.m_within hW hm
  exact reqFactIn_within ⟨hmw.1, hmw.2.1⟩ hW.2.2.2.2.2.2.2.1 h

/-- One step of `K`'s fold (the Lean's lambda). -/
def kStep (fm : AppendFact) (l0 : List Entry) (acc : Option Int) (i : Nat) : EvalM (Option Int) := do
  if acc.isSome then return acc
  let k : Int := (i : Int) + 1
  let y := fm.prevLogIndex + k
  if (← orM (pure (decide (y > l0.length)))
        (do pure ((← atE l0 y).term != (fm.entries[i]!).term))) then return some k
  return none

theorem OnDisk.K_eq (x : OnDisk) : x.K = (do
    let fm ← x.fm
    let r ← (List.range fm.entries.length).foldlM (kStep fm x.L0) none
    pure (r.getD ((fm.entries.length : Int) + 1))) := rfl

theorem kStep_fold_some (fm : AppendFact) (l0 : List Entry) (k : Int) (l : List Nat) :
    l.foldlM (kStep fm l0) (some k) = .ok (some k) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.foldlM_cons, kStep, ih]

/-- `K`'s fold: a found `k` is in `1..n`. -/
theorem kStep_fold_bounds (fm : AppendFact) (l0 : List Entry) (n : Nat) :
    ∀ (l : List Nat) (acc r : Option Int), (∀ i ∈ l, i < n) →
      (∀ k, acc = some k → 1 ≤ k ∧ k ≤ n) → l.foldlM (kStep fm l0) acc = .ok r →
      ∀ k, r = some k → 1 ≤ k ∧ k ≤ n := by
  intro l
  induction l with
  | nil => intro acc r _ hacc h; cases h; exact hacc
  | cons i l ih =>
    intro acc r hl hacc h
    rw [List.foldlM_cons] at h
    obtain ⟨a, ha, h⟩ := bind_ok h
    refine ih a r (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_ h
    intro k hk
    unfold kStep at ha
    cases acc with
    | some k' =>
      simp at ha; subst ha; exact hacc k hk
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at ha
      obtain ⟨c, -, ha⟩ := bind_ok ha
      have hi := hl i List.mem_cons_self
      cases c
      · simp at ha; subst ha; cases hk
      · simp at ha; subst ha; cases hk; omega

/-- `K` is in `1..Len(fm.entries) + 1`. -/
theorem OnDisk.K_bounds {x : OnDisk} {fm : AppendFact} {k : Int} (hfm : x.fm = .ok fm) (h : x.K = .ok k) :
    1 ≤ k ∧ k ≤ fm.entries.length + 1 := by
  rw [OnDisk.K_eq] at h
  obtain ⟨fm', hfm', h⟩ := bind_ok h
  rw [hfm] at hfm'; cases hfm'
  obtain ⟨r, hr, h⟩ := bind_ok h
  simp only [pure_ok, Except.ok.injEq] at h
  subst h
  have := kStep_fold_bounds fm x.L0 fm.entries.length (List.range fm.entries.length) none r
    (fun i hi => List.mem_range.1 hi) (fun k hk => by cases hk) hr
  cases r with
  | none => simp only [Option.getD_none]; omega
  | some k' => have := this k' rfl; simp; omega

theorem Event.Within.entries_le {b E : Nat} {ev : Event} {es : List Entry} (h : ev.Within b E)
    (hes : ev.entries = some es) : es.length ≤ b := by
  have := h.2.1; unfold Event.size at this; rw [hes] at this; simp at this; omega

/-- `es`'s entries: no more than `b`. -/
theorem OnDisk.es_le {x : OnDisk} {b E : Nat} {es : List Entry} (hW : x.Within b E) (h : x.es = .ok es) :
    es.length ≤ b := by
  unfold OnDisk.es at h
  obtain ⟨c, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨fm, hfm, h⟩ := bind_ok h
    obtain ⟨k, -, h⟩ := bind_ok h
    exact Nat.le_trans (subSeq_length_le h) (OnDisk.fm_within hW hfm).2.1
  · split at h
    · cases h; simp
    · exact Event.Within.entries_le hW.2.1 (need_ok h)

theorem OnDisk.L0_le {x : OnDisk} {b E : Nat} (hW : x.Within b E) : x.L0.length ≤ b := by
  unfold OnDisk.L0
  by_cases hn : x.n < x.s.log.length
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    exact (hW.1.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hn)).1
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

/-- `first` above `-2^61` and below `2^62`. -/
theorem OnDisk.first_bounds {x : OnDisk} {b E : Nat} {v : Int} (hb : ((b + 1 : Nat) : Int) < numBound)
    (hW : x.Within b E) (h : x.first = .ok v) : -2 ^ 61 < v ∧ v < 2 ^ 62 := by
  unfold numBound at hb
  unfold OnDisk.first at h
  obtain ⟨c, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨fm, hfm, h⟩ := bind_ok h
    obtain ⟨k, hk, h⟩ := bind_ok h
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    have hfw := OnDisk.fm_within hW hfm
    have hkb := OnDisk.K_bounds hfm hk
    unfold numOk numBound at hfw; omega
  · split at h
    · rename_i hf
      have hn := hW.2.1.1.2.2.1
      cases hx : x.w.first with
      | none => rw [hx] at hf; cases hf
      | some y =>
        have hy := need_ok h; rw [hx] at hy; cases hy
        rw [show x.w = x.q.ev from rfl] at hx
        rw [hx] at hn
        unfold optNumOk numOk numBound at hn; omega
    · simp only [pure_ok, Except.ok.injEq] at h
      subst h
      have hl : x.L0.length ≤ b := by
        unfold OnDisk.L0
        by_cases hn : x.n < x.s.log.length
        · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn]
          exact (hW.1.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hn)).1
        · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          exact Nat.zero_le _
      omega

theorem OnDisk.f_within {x : OnDisk} {b E : Nat} {f : AppendFact} (hb : ((b + 1 : Nat) : Int) < numBound)
    (hW : x.Within b E) (h : x.f = .ok f) :
    bigOk f.prevLogIndex ∧ f.entries.length ≤ b ∧ bigOk f.commit := by
  unfold OnDisk.f at h
  obtain ⟨ld, -, h⟩ := bind_ok h
  split at h
  · have hesb : ∀ es, x.es = .ok es → es.length ≤ b := fun es h => OnDisk.es_le hW h
    have hfb : ∀ v, x.first = .ok v → -2 ^ 61 < v ∧ v < 2 ^ 62 := fun v h => OnDisk.first_bounds hb hW h
    have hcb : ∀ c, need x.w.commit = .ok c → numOk c := by
      intro c hc
      have hn := hW.2.1.1.2.1
      rw [show x.w = x.q.ev from rfl, need_ok hc] at *
      rw [need_ok hc] at hn; exact hn
    obtain ⟨t1, -, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    have hesl := hesb es hes
    dsimp only at h
    obtain ⟨st', hst, h⟩ := bind_ok h
    have hb0 : bigOk 0 := by unfold bigOk; omega
    have hfi : ∀ fi, x.first = .ok fi → bigOk (fi - 1) := by
      intro fi h; have := hfb fi h; unfold bigOk; omega
    have hcc : ∀ c, need x.w.commit = .ok c → bigOk c := by
      intro c h; have := hcb c h; unfold numOk numBound at this; unfold bigOk; omega
    cases hm : x.moved with
    | error e => cases st' <;> cases hfirst : x.first <;> cases hg : x.ll.get t1 <;> cases hh : x.ll.has t1 <;>
        simp [hst, hfirst, hg, hh, hm, andM] at h
    | ok mv =>
    cases hc : need x.w.commit with
    | error e =>
      cases mv
      · cases st' <;> cases hfirst : x.first <;> cases hg : x.ll.get t1 <;> cases hh : x.ll.has t1 <;>
          simp [hst, hfirst, hg, hh, hm, hc, andM] at h <;> (cases h; exact ⟨by first | exact hb0 | exact hfi _ hfirst, hesl, hb0⟩)
      · cases st' <;> cases hfirst : x.first <;> cases hg : x.ll.get t1 <;> cases hh : x.ll.has t1 <;>
          simp [hst, hfirst, hg, hh, hm, hc, andM] at h
    | ok c =>
    cases st' <;> cases hfirst : x.first <;> cases hg : x.ll.get t1 <;> cases hh : x.ll.has t1 <;> cases mv <;>
      simp [hst, hfirst, hg, hh, hm, hc, andM] at h <;>
      (cases h; exact ⟨by first | exact hb0 | exact hfi _ hfirst, hesl, by first | exact hb0 | exact hcc _ hc⟩)
  · have := OnDisk.fm_within hW h
    unfold numOk numBound at this; unfold bigOk; omega

end AntCheck
end EtcdGrove
end Perennial
