/-
**A log's watch events are positive** (pure; stage 2 of the mvcc API proof, the watch chain:
`notes/mvcc-api-invariants.md`, "Hand-off: stage 2, exactness per watcher", (e); 2026-11-05).
Lean-first (no Rocq counterpart).

`wsRecvOk`'s first conjunct asks of every event received a positive revision and, for a put, a
positive creation revision and version (`respShape`'s last conjunct, `Api/SentInv.lean`). They are
true of every event of a log whose revision `0` is empty, with fewer than `2 ^ 63` revisions and
fewer than `2 ^ 63 - 1` changes (a version counts a key's puts, so is at most the changes):
`logEvents_pos`, and `watchEvents_pos`, `filtered_pos` of its sub-lists. A sealed log has them
(`idxSealed`: `LogWf'`, its length, its receipt `⧖ (logCh log)` below the receipts' bound, which a
store's invariant bounds by `2 ^ 48`). A doomed watcher's events are a sub-list of such a log's
(`syncWatchers`' scan), so the same lemma serves for them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris go_etcd_io.etcd.server.v3.storage.mvcc

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **An event is positive**: its revision, and a put's creation revision and version
(`respShape`'s last conjunct). -/
def evPos (ev : EvM) : Prop :=
  0 < sint.Z ev.kv.modRev ∧ (ev.del = false → 0 < sint.Z ev.kv.createRev ∧ 0 < sint.Z ev.kv.version)

/-- A key-value's revisions in `[1, R]` and its version in `[1, V]`. -/
def kvPos (R V : Nat) (v : EtcdKv) : Prop :=
  0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ R ∧ 0 < sint.Z v.modRev ∧ sint.Z v.modRev ≤ R ∧
    0 < sint.Z v.version ∧ sint.Z v.version ≤ V

theorem kvPos_mono {R R' V V' : Nat} {v : EtcdKv} (hR : R ≤ R') (hV : V ≤ V') (h : kvPos R V v) :
    kvPos R' V' v := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, by omega, h3, by omega, h5, by omega⟩

theorem sint_W64_nat (n : Nat) (h : n < 2 ^ 63) : sint.Z (W64 (n : Int)) = n := by
  word

/-- One change of revision `r` keeps every key-value positive, its version bound one more. -/
theorem applyChange_pos {R V r : Nat} (hr1 : 1 ≤ r) (hrR : r ≤ R) (hR : R < 2 ^ 63)
    (hV : V + 1 < 2 ^ 63) (s : List EtcdKv) (hs : ∀ v ∈ s, kvPos R V v) (c : Change) :
    ∀ v ∈ applyChange (W64 (r : Int)) s c, kvPos R (V + 1) v := by
  have hrz : sint.Z (W64 (r : Int)) = r := sint_W64_nat r (by omega)
  intro x hx
  cases c with
  | put k val l =>
    simp only [applyChange, putKv] at hx
    rcases btInsert_mem hx with rfl | h
    · split
      · rename_i v hv
        have hvm : v ∈ s := List.mem_of_find?_eq_some hv
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs v hvm
        have hvz : sint.Z (v.version + W64 1) = sint.Z v.version + 1 := by word
        refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> simp only [hrz, hvz] <;> omega
      · have h1z : sint.Z (W64 1) = 1 := rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hrz, h1z] <;> omega
    · exact kvPos_mono (Nat.le_refl _) (Nat.le_succ _) (hs x h)
  | del k => exact kvPos_mono (Nat.le_refl _) (Nat.le_succ _) (hs x (List.mem_filter.1 hx).1)

/-- A revision's changes keep every key-value positive, its version bound the changes more. -/
theorem applyChanges_pos {R r : Nat} (hr1 : 1 ≤ r) (hrR : r ≤ R) (hR : R < 2 ^ 63) :
    ∀ (cs : List Change) (V : Nat), V + cs.length < 2 ^ 63 → ∀ s : List EtcdKv,
      (∀ v ∈ s, kvPos R V v) → ∀ v ∈ applyChanges (W64 (r : Int)) s cs, kvPos R (V + cs.length) v
  | [], V, _, s, hs => by simpa [applyChanges] using hs
  | c :: cs, V, hV, s, hs => by
    unfold applyChanges
    rw [List.foldl_cons]
    have h1 := applyChange_pos hr1 hrR hR (by simp at hV; omega) s hs c
    have := applyChanges_pos (R := R) hr1 hrR hR cs (V + 1) (by simp at hV; omega) _ h1
    simpa [applyChanges, Nat.add_assoc, Nat.add_comm 1] using this

/-- Induction on a list from its end. -/
theorem posSnocInd {α : Type _} {P : List α → Prop} (nil : P [])
    (snoc : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a t ih => rw [List.reverse_cons]; exact snoc _ _ ih

/-- **Every key-value of a log's state is positive** (revision `0` empty, fewer than `2 ^ 63`
revisions and `2 ^ 63` changes): its revisions below the log's length, its version at most the
changes. -/
theorem stateAfter_pos (L : Log) (h0 : L.getD 0 [] = []) (hlen : L.length < 2 ^ 63)
    (hch : logCh L < 2 ^ 63) : ∀ v ∈ stateAfter L, kvPos (L.length - 1) (logCh L) v := by
  revert h0 hlen hch
  refine posSnocInd (P := fun L => L.getD 0 [] = [] → L.length < 2 ^ 63 →
    logCh L < 2 ^ 63 → ∀ v ∈ stateAfter L, kvPos (L.length - 1) (logCh L) v) ?_ ?_ L
  · intro _ _ _ v hv; simp [stateAfter] at hv
  · intro L cs ih h0 hlen hch
    rw [stateAfter_append, logCh_snoc]
    rw [logCh_snoc] at hch
    simp only [List.length_append, List.length_singleton] at hlen ⊢
    by_cases hL : L = []
    · subst hL
      have : cs = [] := by simpa using h0
      subst this
      intro v hv; simp [applyChanges, stateAfter] at hv
    · have hpos : 0 < L.length := List.length_pos_iff.2 hL
      have h0' : L.getD 0 [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hpos] at h0
        rwa [List.getD_eq_getElem?_getD]
      have IH := ih h0' (by omega) (by omega)
      have IH' : ∀ v ∈ stateAfter L, kvPos (L.length + 1 - 1) (logCh L) v :=
        fun v hv => kvPos_mono (by omega) (Nat.le_refl _) (IH v hv)
      exact applyChanges_pos (R := L.length + 1 - 1) (r := L.length) (by omega) (by omega)
        (by omega) cs (logCh L) (by omega) _ IH'

theorem logCh_take_le (L : Log) (n : Nat) : logCh (L.take n) ≤ logCh L := by
  have h := congrArg logCh (List.take_append_drop n L)
  unfold logCh at h ⊢
  rw [List.map_append, List.sum_append] at h
  omega

theorem logCh_getD_le (L : Log) (m : Nat) : logCh (L.take m) + (L.getD m []).length ≤ logCh L := by
  by_cases hm : m < L.length
  · have h := congrArg logCh (List.take_append_drop m L)
    rw [List.drop_eq_getElem_cons hm] at h
    unfold logCh at h ⊢
    rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    simp only [Option.getD_some]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simpa using logCh_take_le L m

/-- **Every event of a log is positive** (see the file header). -/
theorem logEvents_pos (L : Log) (h0 : L.getD 0 [] = []) (hlen : L.length < 2 ^ 63)
    (hch : logCh L + 1 < 2 ^ 63) (lo hi : Nat) : ∀ ev ∈ logEvents L lo hi, evPos ev := by
  intro ev hev
  unfold logEvents at hev
  simp only [List.mem_flatten, List.mem_map, List.mem_range'] at hev
  obtain ⟨_, ⟨m, -, rfl⟩, hev⟩ := hev
  unfold evsOfRevM at hev
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hev
  obtain ⟨i, hi, kv, hkv, rfl⟩ := hev
  -- the revision is a non-empty one of the log: `1 ≤ m < |L|`
  have hne : L.getD m [] ≠ [] := by intro h; rw [h] at hi; simp at hi
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd h0 hne
    · exact h
  have hmL : m < L.length := by
    refine Classical.byContradiction fun hc => hne ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have hmz : sint.Z (W64 (m : Int)) = m := sint_W64_nat m (by omega)
  -- the state before the revision is positive
  have hbefore : ∀ v ∈ stateAt L (m - 1), kvPos m (logCh (L.take m)) v := by
    intro v hv
    unfold stateAt at hv
    rw [show m - 1 + 1 = m by omega] at hv
    have hm0 : (L.take m).getD 0 [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left_of_eq_true _ _ (by simp; omega)]
      rwa [← List.getD_eq_getElem?_getD]
    have := stateAfter_pos (L.take m) hm0 (by simp; omega)
      (by have := logCh_take_le L m; omega) v hv
    exact kvPos_mono (by simp; omega) (Nat.le_refl _) this
  have hgd := logCh_getD_le L m
  unfold changeKv at hkv
  split at hkv
  · -- a put: the key-value the revision wrote, in the state after it
    rename_i k val l hc
    have hmem : kv ∈ applyChanges (W64 (m : Int)) (stateAt L (m - 1)) ((L.getD m []).take (i + 1)) :=
      List.mem_of_find?_eq_some hkv
    have hp := applyChanges_pos (R := m) (r := m) hm1 (Nat.le_refl _) (by omega)
      ((L.getD m []).take (i + 1)) (logCh (L.take m))
      (by have := List.length_take_le (i + 1) (L.getD m []); omega) _ hbefore kv hmem
    obtain ⟨h1, -, h3, -, h5, -⟩ := hp
    unfold evOfKv evPos
    split
    · rename_i hcz
      rw [hcz] at h1; exact absurd h1 (by decide)
    · exact ⟨h3, fun _ => ⟨h1, h5⟩⟩
  · -- a delete: the key alone, at the revision
    cases hkv
    unfold evOfKv evPos zeroKv
    simp only [ite_true]
    refine ⟨?_, fun h => by cases h⟩
    show 0 < sint.Z (W64 (m : Int)); rw [hmz]; omega
  · cases hkv

/-- The range's events of a log are positive. -/
theorem watchEvents_pos (L : Log) (h0 : L.getD 0 [] = []) (hlen : L.length < 2 ^ 63)
    (hch : logCh L + 1 < 2 ^ 63) (r : WatchRange) (lo hi : Nat) :
    ∀ ev ∈ watchEvents L r lo hi, evPos ev := fun ev hev =>
  logEvents_pos L h0 hlen hch lo hi ev (List.mem_filter.1 hev).1

/-- The events the filters keep of positive events are positive. -/
theorem filtered_pos (fs : List (EvM → Bool)) (evs : List EvM) (h : ∀ ev ∈ evs, evPos ev) :
    ∀ ev ∈ filtered fs evs, evPos ev := fun ev hev => h ev (List.mem_filter.1 hev).1

/-- `LogWf'`'s revision `0`. -/
theorem LogWf'.getD_zero {L : Log} (h : LogWf' L) : L.getD 0 [] = [] := by
  by_cases hL : L = []
  · subst hL; rfl
  · rw [List.getD_eq_getElem?_getD, h.1 hL]; rfl

end mvcc
end EtcdGrove
end Perennial
