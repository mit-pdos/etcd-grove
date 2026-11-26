/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: a `ready`'s safety checks pass (#33 S4)

`OnDisk`'s safety checks (B 422-436: `CommitSafety`, `LeaderCompleteness`, `LogMatching`,
`CommittedEntriesPreserved`) evaluated on reported logs (`logOf`): two logs that agree wherever
their terms do (raft's `logRecs_agree`, `RaftLaws`) are `Matching` (B 132); a prefix is
`IsPrefix` (R 130); prefixes of one log are `Comparable` (B 130); comparing reported logs never
errs. The kind lemmas of `ReadyOD.lean`/`ReadyOD2.lean` take these as hypotheses.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Logs

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section safe
variable [GooseExts]

/-- A prefix is `IsPrefix` (R 130). -/
theorem isPrefix_of_prefix {a b : List Entry} (h : a <+: b) : isPrefix a b = .ok true := by
  obtain ⟨t, rfl⟩ := h
  unfold isPrefix
  have hk : a.length ≤ (a ++ t).length := by simp
  rw [if_pos (by exact_mod_cast hk), subSeq_one _ _ hk, eok_bind, List.take_left' rfl]
  exact entriesEqual_self _

/-- Two prefixes of one log are `Comparable` (B 130). -/
theorem comparable_of_prefix {a b l : List Entry} (ha : a <+: l) (hb : b <+: l) :
    comparable a b = .ok true := by
  unfold comparable
  by_cases hl : a.length ≤ b.length
  · rw [isPrefix_of_prefix (List.prefix_of_prefix_length_le ha hb hl)]; rfl
  · have h2 : isPrefix a b = .ok false := by
      unfold isPrefix; rw [if_neg (by omega)]; rfl
    rw [h2, orM_false]
    exact isPrefix_of_prefix (List.prefix_of_prefix_length_le hb ha (by omega))

theorem entOf_equal (e f : EntryM) : ∃ x, (entOf e).equal (entOf f) = .ok x := by
  unfold Entry.equal
  split
  · exact ⟨_, rfl⟩
  · unfold Value.equal
    have he : (entOf e).value.isRec = false := by unfold entOf; split <;> (try split) <;> rfl
    have hf : (entOf f).value.isRec = false := by unfold entOf; split <;> (try split) <;> rfl
    rw [he, hf]
    exact ⟨_, rfl⟩

/-- Comparing reported logs never errs. -/
theorem entriesEqual_logOf (a b : List EntryM) : ∃ x, entriesEqual (logOf a) (logOf b) = .ok x := by
  unfold entriesEqual
  split
  · exact ⟨_, rfl⟩
  · rename_i hlen; clear hlen
    induction a generalizing b with
    | nil => exact ⟨_, rfl⟩
    | cons e a ih =>
      cases b with
      | nil => exact ⟨_, rfl⟩
      | cons f b =>
        show ∃ x, entriesEqualAux (entOf e :: logOf a) (entOf f :: logOf b) = .ok x
        unfold entriesEqualAux
        obtain ⟨y, hy⟩ := entOf_equal e f
        rw [hy, eok_bind]
        cases y
        · exact ⟨_, rfl⟩
        · simpa using ih b

theorem uZ_inj {x y : w64} (h : uint.Z x = uint.Z y) : x = y := by word

/-- **`Matching` (B 132-134) of two reported logs** that agree up to wherever their terms do
(`RaftLaws`' log matching for two certified logs). -/
theorem matching_logOf {a b : List EntryM}
    (h : ∀ (k : Nat) (e f : EntryM), a[k]? = some e → b[k]? = some f → e.Term' = f.Term' →
      a.take (k + 1) = b.take (k + 1)) :
    matching (logOf a) (logOf b) = .ok true := by
  unfold matching
  have step : ∀ i, i < min (logOf a).length (logOf b).length →
      (if ((logOf a)[i]!).term == ((logOf b)[i]!).term then do
        if !(← ((logOf a)[i]!).equal ((logOf b)[i]!)) then return false
        if i > 0 && ((logOf a)[i - 1]!).term != ((logOf b)[i - 1]!).term then return false
        return true
      else (return true : EvalM Bool)) = .ok true := by
    intro i hi
    rw [logOf_length, logOf_length] at hi
    obtain ⟨e, he⟩ : ∃ e, a[i]? = some e := ⟨a[i], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨f, hf⟩ : ∃ f, b[i]? = some f := ⟨b[i], List.getElem?_eq_getElem (by omega)⟩
    rw [logOf_getElem! he, logOf_getElem! hf, entOf_term, entOf_term]
    by_cases ht : uint.Z e.Term' = uint.Z f.Term'
    · rw [if_pos (by simpa using ht)]
      have htk := h i e f he hf (uZ_inj ht)
      have hef : e = f := by
        have h1 := congrArg (fun l => l[i]?) htk
        simp only [List.getElem?_take, show i < i + 1 by omega, ite_true, he, hf] at h1
        exact Option.some.inj h1
      subst hef
      simp only [entry_equal_self, eok_bind, Bool.not_true, Bool.false_eq_true, ite_false]
      by_cases hi0 : i > 0
      · obtain ⟨e', he'⟩ : ∃ e', a[i - 1]? = some e' := ⟨a[i - 1], List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨f', hf'⟩ : ∃ f', b[i - 1]? = some f' := ⟨b[i - 1], List.getElem?_eq_getElem (by omega)⟩
        have h1 := congrArg (fun l => l[i - 1]?) htk
        simp only [List.getElem?_take, show i - 1 < i + 1 by omega, ite_true, he', hf'] at h1
        have : e' = f' := Option.some.inj h1
        subst this
        rw [logOf_getElem! he', logOf_getElem! hf']
        simp [epure]
      · simp [hi0, epure]
    · rw [if_neg (by simpa using ht)]; rfl
  generalize hl : List.range (min (logOf a).length (logOf b).length) = l
  have hl' : ∀ i ∈ l, i < min (logOf a).length (logOf b).length := by
    intro i hi; rw [← hl] at hi; exact List.mem_range.mp hi
  clear hl
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldlM_cons]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [step i (hl' i (List.mem_cons_self ..)), eok_bind]
    exact ih (fun j hj => hl' j (List.mem_cons_of_mem _ hj))

theorem uZ_toNat_nat (c : w64) : (uint.Z c).toNat = uint.nat c := by word

theorem logOf_take (l : List EntryM) (k : Nat) : (logOf l).take k = logOf (l.take k) := by
  unfold logOf; rw [List.map_take]

theorem logOf_prefix {a b : List EntryM} (h : a <+: b) : logOf a <+: logOf b := h.map _

/-! ## The checks on a node's new log `L` with commit `c` at term `T`, from raft's facts -/

/-- `CommitSafety` (B 424): `chain` (a prefix of the committed log, C5) and the new committed
prefix (the committed log's, `ReadyFacts`) are comparable. -/
theorem cs_ok {G : RaftFacts} {ch : List Entry} {L : List EntryM} {c : w64}
    (hch : ∃ c' ≤ G.committed.length, ch = logOf (G.committed.take c'))
    (hcG : L.take (uint.nat c) = G.committed.take (uint.nat c)) :
    comparable ch ((logOf L).take (uint.Z c).toNat) = .ok true := by
  obtain ⟨c', -, rfl⟩ := hch
  rw [uZ_toNat_nat, logOf_take, hcG]
  exact comparable_of_prefix (logOf_prefix (List.take_prefix _ _)) (logOf_prefix (List.take_prefix _ _))

/-- `LeaderCompleteness` (B 426-428): the new committed prefix (recorded in term `T`, `ReadyFacts`)
is in every leader log of a later term (each extends its campaign log, C5; `commitIn_camp`,
`RaftLaws`); bootstrapped, the boot record's term `1` is not later than `T`. -/
theorem lc_ok {R : RunCfg} {G : RaftFacts} (hG : RaftLaws G) {ll : TermFn (List Entry)} {L : List EntryM}
    {c T : w64}
    (hll : ∀ p ∈ ll, (R.boot = true ∧ p = (1, logOf (bootLog R))) ∨ ∃ l ∈ G.logs, p.2 = logOf l ∧
      ∃ t l0, uint.Z t = p.1 ∧ (t, l0) ∈ G.camps ∧ l0 <+: l)
    (hcm : (T, uint.nat c) ∈ G.commits)
    (hcG : L.take (uint.nat c) = G.committed.take (uint.nat c))
    (hT1 : R.boot = true → 1 ≤ uint.Z T) :
    ∀ p ∈ ll, p.1 > uint.Z T → isPrefix ((logOf L).take (uint.Z c).toNat) p.2 = .ok true := by
  intro p hp hgt
  rcases hll p hp with ⟨hb, rfl⟩ | ⟨l, -, hpl, t, l0, ht, hcamp, hpre⟩
  · have := hT1 hb; simp only at hgt; omega
  obtain ⟨-, -, -, -, -, hcl, -⟩ := hG
  have := (hcl _ hcm).2 (t, l0) hcamp (by simp only; omega)
  rw [hpl, uZ_toNat_nat, logOf_take, hcG]
  exact isPrefix_of_prefix (logOf_prefix (this.trans hpre))

/-- `CommittedEntriesPreserved`'s `chain` (B 434): `chain`, where it reaches `c`, is the new log's
prefix there. -/
theorem ch_ok {G : RaftFacts} {ch : List Entry} {L : List EntryM} {c : w64}
    (hch : ∃ c' ≤ G.committed.length, ch = logOf (G.committed.take c'))
    (hcG : L.take (uint.nat c) = G.committed.take (uint.nat c)) :
    uint.Z c ≤ ch.length → ch.take (uint.Z c).toNat = (logOf L).take (uint.Z c).toNat := by
  obtain ⟨c', hc', rfl⟩ := hch
  intro hl
  rw [logOf_length, List.length_take] at hl
  rw [uZ_toNat_nat, logOf_take, logOf_take, hcG, List.take_take]
  have : min (uint.nat c) c' = uint.nat c := by
    have := uZ_toNat_nat c; have : 0 ≤ uint.Z c := by word
    omega
  rw [this]

/-- `LogMatching` (B 430-432): the new log (certified, `ReadyFacts`) matches every node's
(certified, C5), by raft's log matching (`RaftLaws`). -/
theorem lm_ok {G : RaftFacts} (hG : RaftLaws G) {S : State} {L : List EntryM} (hL : L ∈ G.logs) {N : Nat}
    (hlogs : ∀ n : Fin N, ∃ l ∈ G.logs, S.log[n.val]! = logOf l) (hlen : S.log.length = N) :
    ∀ b : Nat, matching (logOf L) (S.log[b]!) = .ok true := by
  intro b
  by_cases hb : b < N
  · obtain ⟨l, hl, he⟩ := hlogs ⟨b, hb⟩
    rw [show S.log[b]! = logOf l from he]
    exact matching_logOf (fun k e f he hf ht => hG.2.2.1 L hL l hl k e f he hf ht)
  · have : S.log[b]! = logOf [] := by
      rw [getElem!_def, List.getElem?_eq_none (by omega)]; rfl
    rw [this]
    exact matching_logOf (fun k e f _ hf _ => by simp at hf)

end safe

end AntSim
end EtcdGrove
end Perennial
