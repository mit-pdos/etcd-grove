/-
Pure lemmas of `array.Allocate`: its scan for a run of consecutive free ids (`scanInv`, the
state of the scan before position `k`; `scan_run`, one step of it) and the removal of the run
found (`run_remove`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayModel
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

theorem getD_of_some {f : List w64} {k : Nat} {x : w64} (h : f[k]? = some x) :
    f.getD k 0 = x := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Consecutive ids from `st` on rise by one each. -/
theorem consec_sum {f : List w64} {st : Nat} : ∀ m : Nat,
    (∀ j, st ≤ j → j < st + m → consec f j) →
    uint.Z (f.getD (st + m) 0) = uint.Z (f.getD st 0) + m
  | 0, _ => by simp
  | m + 1, h => by
    have ih := consec_sum (f := f) (st := st) m (fun j h1 h2 => h j h1 (by omega))
    have hc := h (st + m) (by omega) (by omega)
    unfold consec at hc
    rw [show st + (m + 1) = st + m + 1 by omega, hc, ih]
    omega

/-- The scan at `k`, its current run starting at `st` (at `0` or after a gap): a run of `n`
ends at `k` iff the current run has length `n` (none ended before). -/
theorem scan_core {f : List w64} {n k st : Nat} (hn : 1 ≤ n) (hst : st ≤ k) (hk : k < f.length)
    (hcons : ∀ j, st ≤ j → j < k → consec f j) (hmax : st = 0 ∨ ¬ consec f (st - 1))
    (hno : ∀ i' < k, ¬ runEnd f n i') : runEnd f n k ↔ k - st + 1 = n := by
  constructor
  · rintro ⟨h1, -, h3⟩
    rcases Nat.lt_or_ge (k - st + 1) n with hlt | hge
    · rcases hmax with h0 | hnc
      · omega
      · exact absurd (h3 (st - 1) (by omega) (by omega)) hnc
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · exact heq.symm
      · exact absurd ⟨by omega, by omega, fun j hj1 hj2 => hcons j (by omega) (by omega)⟩
          (hno (k - 1) (by omega))
  · intro heq
    exact ⟨by omega, hk, fun j _ hj2 => hcons j (by omega) hj2⟩

/-- The state of `array.Allocate`'s scan before position `k`: `previd` is the id before it
(`0` at the start), `initial` the first of the run it ends, which starts at `0` or after a
gap. -/
def scanInv (f : List w64) (k : Nat) (previd initial : w64) : Prop :=
  (k = 0 ∧ previd = W64 0) ∨
  (0 < k ∧ f[k - 1]? = some previd ∧ ∃ st, st < k ∧ f[st]? = some initial ∧
    (∀ j, st ≤ j → j < k - 1 → consec f j) ∧ (st = 0 ∨ ¬ consec f (st - 1)))

theorem scanInv_zero (f : List w64) (initial : w64) : scanInv f 0 (W64 0) initial :=
  Or.inl ⟨rfl, rfl⟩

theorem scan_step {f : List w64} {k : Nat} {id previd initial : w64} (hinc : PgidsIncr f)
    (hge : ∀ x ∈ f, 2 ≤ uint.Z x) (hk : f[k]? = some id) (hinv : scanInv f k previd initial) :
    ∃ st, st ≤ k ∧ f[st]? = some (if previd = W64 0 ∨ id - previd ≠ W64 1 then id else initial) ∧
      (∀ j, st ≤ j → j < k → consec f j) ∧ (st = 0 ∨ ¬ consec f (st - 1)) := by
  rcases hinv with ⟨rfl, rfl⟩ | ⟨hk0, hprev, st, hst, hini, hcons, hmax⟩
  · refine ⟨0, Nat.le_refl 0, ?_, fun j _ h2 => by omega, Or.inl rfl⟩
    rw [if_pos (Or.inl rfl)]; exact hk
  · obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.1 hprev
    obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.1 hk
    have hlt := List.pairwise_iff_getElem.1 hinc (k - 1) k h1 h2 (by omega)
    rw [e1, e2] at hlt
    have hp2 : 2 ≤ uint.Z previd := hge _ (List.mem_of_getElem? hprev)
    have hcon_iff : consec f (k - 1) ↔ id - previd = W64 1 := by
      unfold consec
      rw [show k - 1 + 1 = k by omega, getD_of_some hk, getD_of_some hprev]
      constructor <;> intro h <;> word
    by_cases hc : id - previd = W64 1
    · have hpv0 : previd ≠ W64 0 := by intro h; rw [h] at hp2; word
      rw [if_neg (by rintro (h | h); exact hpv0 h; exact h hc)]
      refine ⟨st, by omega, hini, fun j h1 h2 => ?_, hmax⟩
      by_cases hj : j < k - 1
      · exact hcons j h1 hj
      · rw [show j = k - 1 by omega]; exact hcon_iff.2 hc
    · rw [if_pos (Or.inr hc)]
      exact ⟨k, Nat.le_refl k, hk, fun j h1 h2 => by omega,
        Or.inr (fun h => hc (hcon_iff.1 h))⟩

/-- One step of `array.Allocate`'s scan, at `k` (holding `id`; no run of `n` ended before):
the run's first id `initial'` (`id` after a gap), and whether a run of `n` ends here. -/
theorem scan_run {f : List w64} {n k : Nat} {id previd initial : w64} (hn : 1 ≤ n)
    (hinc : PgidsIncr f) (hge : ∀ x ∈ f, 2 ≤ uint.Z x) (hk : f[k]? = some id)
    (hinv : scanInv f k previd initial) (hno : ∀ i' < k, ¬ runEnd f n i') :
    scanInv f (k + 1) id (if previd = W64 0 ∨ id - previd ≠ W64 1 then id else initial) ∧
    uint.Z (if previd = W64 0 ∨ id - previd ≠ W64 1 then id else initial) ≤ uint.Z id ∧
    (runEnd f n k ↔
      uint.Z id - uint.Z (if previd = W64 0 ∨ id - previd ≠ W64 1 then id else initial) + 1 = n) := by
  obtain ⟨st, hst, hini, hcons, hmax⟩ := scan_step hinc hge hk hinv
  have hkl : k < f.length := (List.getElem?_eq_some_iff.1 hk).1
  have hsum := consec_sum (f := f) (st := st) (k - st) (fun j h1 h2 => hcons j h1 (by omega))
  rw [show st + (k - st) = k by omega, getD_of_some hk, getD_of_some hini] at hsum
  refine ⟨Or.inr ⟨by omega, by simpa using hk, st, by omega, hini,
    fun j h1 h2 => hcons j h1 (by omega), hmax⟩, by omega, ?_⟩
  rw [scan_core hn hst hkl hcons hmax hno]
  omega

/-- No run of `n` ends before the end of `f`: none at all. -/
theorem runEnd_none {f : List w64} {n : Nat} (h : ∀ i' < f.length, ¬ runEnd f n i') (i : Nat) :
    ¬ runEnd f n i := fun hr => h i hr.2.1 hr

/-- The ids of a run of `n` ending at `i` (from `r`, at `i + 1 - n`) in increasing ids: they
are the `n` ids from `r` on, and removing them leaves those before and after. -/
theorem run_remove {f : List w64} {n i : Nat} {r : w64} (hn : 1 ≤ n) (hinc : PgidsIncr f)
    (hrun : runEnd f n i) (hr : f[i + 1 - n]? = some r) :
    uint.Z r + n ≤ 2 ^ 64 ∧ (∀ x, inRun r n x → x ∈ f) ∧
    f.filter (fun x => decide ¬ inRun r n x) = f.take (i + 1 - n) ++ f.drop (i + 1) := by
  obtain ⟨h1, hi, h3⟩ := hrun
  have hval : ∀ p, i + 1 - n ≤ p → p ≤ i → uint.Z (f.getD p 0) = uint.Z r + (p - (i + 1 - n)) := by
    intro p hp1 hp2
    have := consec_sum (f := f) (st := i + 1 - n) (p - (i + 1 - n))
      (fun j hj1 hj2 => h3 j hj1 (by omega))
    rw [show i + 1 - n + (p - (i + 1 - n)) = p by omega, getD_of_some hr] at this
    omega
  have hlast := hval i (by omega) (Nat.le_refl i)
  have hlast_bd : uint.Z (f.getD i 0) < 2 ^ 64 := by word
  -- position order is value order
  have hlt : ∀ p q (hp : p < f.length) (hq : q < f.length), p < q → uint.Z f[p] < uint.Z f[q] :=
    fun p q hp hq hpq => List.pairwise_iff_getElem.1 hinc p q hp hq hpq
  refine ⟨by omega, fun x ⟨hx1, hx2⟩ => ?_, ?_⟩
  · obtain ⟨p, hpdef⟩ : ∃ p, p = i + 1 - n + (uint.Z x - uint.Z r).toNat := ⟨_, rfl⟩
    have hp : p < f.length := by omega
    have hd := hval p (by omega) (by omega)
    rw [getD_of_lt 0 hp] at hd
    have hx : f[p] = x := BitVec.eq_of_toNat_eq (by word)
    exact hx ▸ List.getElem_mem hp
  · have hri : r = f[i + 1 - n]'(by omega) := ((List.getElem?_eq_some_iff.1 hr).2).symm
    conv => lhs; rw [← List.take_append_drop (i + 1 - n) f, ← List.take_append_drop n (f.drop (i + 1 - n)),
      List.drop_drop, show i + 1 - n + n = i + 1 by omega]
    rw [List.filter_append, List.filter_append]
    rw [List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.filter_eq_self.2, List.nil_append]
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hx
      simp only [List.getElem_drop, List.length_drop] at hp ⊢
      have := hlt i (i + 1 + p) hi (by omega) (by omega)
      rw [← getD_of_lt 0 hi, hlast] at this
      simp only [decide_eq_true_iff, Classical.not_not]; unfold inRun; word
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hx
      simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_drop] at hp ⊢
      have := hval (i + 1 - n + p) (by omega) (by omega)
      rw [getD_of_lt 0 (by omega)] at this
      simp only [decide_eq_true_iff, Classical.not_not]; unfold inRun; word
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hx
      simp only [List.getElem_take, List.length_take] at hp ⊢
      have := hlt p (i + 1 - n) (by omega) (by omega) (by omega)
      rw [← hri] at this
      simp only [decide_eq_true_iff, Classical.not_not]; unfold inRun; word

/-- The first id of a run of `n` ending at `i` (at `id`) is `id - (n - 1)`. -/
theorem runEnd_start {f : List w64} {n i : Nat} {id initial : w64} (hn : 1 ≤ n)
    (hr : runEnd f n i) (hk : f[i]? = some id) (h : uint.Z id - uint.Z initial + 1 = n) :
    f[i + 1 - n]? = some initial := by
  obtain ⟨h1, hi, h3⟩ := hr
  have hs := consec_sum (f := f) (st := i + 1 - n) (n - 1) (fun j hj1 hj2 => h3 j hj1 (by omega))
  rw [show i + 1 - n + (n - 1) = i by omega, getD_of_some hk, getD_of_lt 0 (by omega)] at hs
  rw [List.getElem?_eq_getElem (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [uint.Z] at h hs
  omega

/-- `copy(s[a:], s[c:])` (`a ≤ c`) then `s[:len(s) - (c - a)]`: the ids before `a` and those
from `c` on. -/
theorem copy_down_take {α : Type} (vs : List α) (a c : Nat) (hac : a ≤ c) (hc : c ≤ vs.length) :
    (vs.take a ++ ((subslice c vs.length vs).take (vs.length - a) ++
      (subslice a vs.length vs).drop (vs.length - c)) ++ vs.drop vs.length).take
      (vs.length - (c - a)) = vs.take a ++ vs.drop c := by
  have h1 : subslice c vs.length vs = vs.drop c := by simp [subslice]
  rw [h1, List.take_of_length_le (l := vs.drop c) (by simp only [List.length_drop]; omega),
    List.drop_length,
    List.append_nil, ← List.append_assoc]
  apply List.take_left'
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

/-- The run from `r` of `j + 1` ids: that of `j`, and `r + j`. -/
theorem inRun_succ {r x j : w64} {n : Nat} (hb : uint.Z r + n ≤ 2 ^ 64) (hj : uint.Z j < n) :
    inRun r (uint.nat j + 1) x ↔ inRun r (uint.nat j) x ∨ x = r + j := by
  unfold inRun
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : uint.Z x < uint.Z r + (uint.nat j : Nat)
    · exact Or.inl ⟨h1, h⟩
    · right; word
  · rintro (⟨h1, h2⟩ | rfl)
    · exact ⟨h1, by word⟩
    · constructor <;> word

end bbolt
end EtcdGrove
end Perennial
