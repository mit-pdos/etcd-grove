/-
The proof of the consistent-cut theorem (`closed_cut`; the disciplines are in `TreeCut.lean`). Pure.
Untrusted.

The argument (`notes/wal-fsext-i2-design.md`, "Implementation log"):
1. *Slots.* By induction along the log, the replay of the kept entries holds in each slot what the
   run held right after the slot's last kept writer (`kept_entry`): a kept entry's slots held, in
   the replay, what they held in the run when it took effect, because every earlier writer of them
   is kept (`PerSlotSeq`, `DirOpExcl`, closure).
2. *Directories.* Let `a` be past the last kept directory operation. Every entry below `a` is kept
   (`DirOpExcl`), so the replay up to `a` is the run's tree `T a`; after `a` only file operations are
   kept, and the run has none but file operations from `a` to past the last kept entry. File
   operations change no entry naming a directory and no directory key, so the replay has `T a`'s.
3. *Files.* A kept file operation keeps the replay's files named once (a create's inode is new, a
   rename moves the one entry naming its file).
-/
module

public import GooseLang.Ext.Fs.TreeCut
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Classical

/-! ## An operation's effect on entries -/

theorem entry_create (j0 : Ino) (b0 : GoString) (i : Ino) (m : Tree) (j : Ino) (b : GoString) :
    ((MetaOp.create j0 b0 i).apply m).entry j b =
      if j0 = j ∧ b0 = b then some (.file i) else m.entry j b := by
  simp only [MetaOp.apply]; rw [entry_upd]
  by_cases hj : j0 = j
  · subst hj; by_cases hb : b0 = b
    · subst hb; simp
    · simp [hb, getD_lookup, Tree.entry]
  · simp [hj]

theorem entry_remove (j0 : Ino) (b0 : GoString) (n : Node) (m : Tree) (j : Ino) (b : GoString) :
    ((MetaOp.remove j0 b0 n).apply m).entry j b =
      if j0 = j ∧ b0 = b then none else m.entry j b := by
  simp only [MetaOp.apply]; rw [entry_upd]
  by_cases hj : j0 = j
  · subst hj; by_cases hb : b0 = b
    · subst hb; simp
    · simp [hb, getD_lookup, Tree.entry]
  · simp [hj]

theorem entry_mkdir (j0 : Ino) (b0 : GoString) (J : Ino) (m : Tree) (j : Ino) (b : GoString) :
    ((MetaOp.mkdir j0 b0 J).apply m).entry j b =
      if J = j then none else if j0 = j ∧ b0 = b then some (.dir J) else m.entry j b := by
  simp only [MetaOp.apply]
  by_cases hJ : J = j
  · subst hJ; simp [Tree.entry]
  · have : Tree.entry (<[J := (∅ : Dir)]> (m.upd j0 (fun d => <[b0 := Node.dir J]> d))) j b =
        (m.upd j0 (fun d => <[b0 := Node.dir J]> d)).entry j b := by
      simp [Tree.entry, hJ]
    rw [this, entry_upd, if_neg hJ]
    by_cases hj : j0 = j
    · subst hj; by_cases hb : b0 = b
      · subst hb; simp
      · simp [hb, getD_lookup, Tree.entry]
    · simp [hj]

theorem entry_rename (j0 : Ino) (b0 : GoString) (j1 : Ino) (b1 : GoString) (n : Node)
    (old : Option Node) (m : Tree) (j : Ino) (b : GoString) :
    ((MetaOp.rename j0 b0 j1 b1 n old).apply m).entry j b =
      match m.entry j0 b0 with
      | none => m.entry j b
      | some n' => if j1 = j ∧ b1 = b then some n' else if j0 = j ∧ b0 = b then none
          else m.entry j b := by
  simp only [MetaOp.apply]
  cases hs : m.entry j0 b0 with
  | none => rfl
  | some n' =>
    show ((m.upd j0 (fun d => GMap.delete b0 d)).upd j1 (fun d => <[b1 := n']> d)).entry j b = _
    have hr := entry_remove j0 b0 n m
    simp only [MetaOp.apply] at hr
    rw [entry_upd]
    by_cases h1 : j1 = j
    · subst h1
      by_cases hb1 : b1 = b
      · subst hb1; simp
      · rw [if_pos rfl, GMap.lookup_insert_ne _ _ hb1, getD_lookup]
        show (m.upd j0 (fun d => GMap.delete b0 d)).entry j1 b = _
        rw [hr]; simp [hb1]
    · rw [if_neg h1, hr]; simp [h1]

/-- An operation leaves the entries it does not write. -/
theorem apply_other (o : MetaOp) (m : Tree) (j : Ino) (b : GoString) (h : ¬ o.Writes j b) :
    (o.apply m).entry j b = m.entry j b := by
  cases o with
  | create j0 b0 i =>
    rw [entry_create, if_neg]
    rintro ⟨rfl, rfl⟩; exact h (.inl (by simp [MetaOp.slots]))
  | mkdir j0 b0 J =>
    rw [entry_mkdir, if_neg (fun hJ => h (.inr ⟨j0, b0, by rw [hJ]⟩)), if_neg]
    rintro ⟨rfl, rfl⟩; exact h (.inl (by simp [MetaOp.slots]))
  | remove j0 b0 n =>
    rw [entry_remove, if_neg]
    rintro ⟨rfl, rfl⟩; exact h (.inl (by simp [MetaOp.slots]))
  | rename j0 b0 j1 b1 n old =>
    rw [entry_rename]
    split
    · rfl
    · rw [if_neg, if_neg]
      · rintro ⟨rfl, rfl⟩; exact h (.inl (by simp [MetaOp.slots]))
      · rintro ⟨rfl, rfl⟩; exact h (.inl (by simp [MetaOp.slots]))

/-- What an operation writes depends only on what its slots held. -/
theorem apply_agree (o : MetaOp) (m1 m2 : Tree)
    (hs : ∀ sl ∈ o.slots, m1.entry sl.1 sl.2 = m2.entry sl.1 sl.2) (j : Ino) (b : GoString)
    (hw : o.Writes j b) : (o.apply m1).entry j b = (o.apply m2).entry j b := by
  cases o with
  | create j0 b0 i =>
    rw [entry_create, entry_create]
    split
    · rfl
    · exact hs (j, b) (by
        rcases hw with h | ⟨_, _, h⟩
        · exact h
        · cases h)
  | mkdir j0 b0 J =>
    rw [entry_mkdir, entry_mkdir]
    split
    · rfl
    · split
      · rfl
      · exact hs (j, b) (by
          rcases hw with h | ⟨_, _, h⟩
          · exact h
          · cases h; contradiction)
  | remove j0 b0 n =>
    rw [entry_remove, entry_remove]
    split
    · rfl
    · exact hs (j, b) (by
        rcases hw with h | ⟨_, _, h⟩
        · exact h
        · cases h)
  | rename j0 b0 j1 b1 n old =>
    have hw' : (j, b) ∈ (MetaOp.rename j0 b0 j1 b1 n old).slots := by
      rcases hw with h | ⟨_, _, h⟩
      · exact h
      · cases h
    rw [entry_rename, entry_rename, hs (j0, b0) (by simp [MetaOp.slots])]
    cases m2.entry j0 b0 with
    | none => exact hs (j, b) hw'
    | some n' =>
      simp only
      split
      · rfl
      · split
        · rfl
        · exact hs (j, b) hw'

/-! ## The run and the replay of the kept entries, step by step -/

section run
variable (T0 : Tree) (log : List LogEntry) (S : Nat → Prop)

/-- The kept operations among the first `t` entries. -/
def keptUpTo (t : Nat) : List MetaOp :=
  (List.range t).filterMap (fun k => if S k then (log[k]?).map (·.op) else none)

theorem prefTree_zero : prefTree T0 log 0 = T0 := by simp [prefTree, replay]

theorem prefTree_succ {t : Nat} {e : LogEntry} (he : log[t]? = some e) :
    prefTree T0 log (t + 1) = e.op.apply (prefTree T0 log t) := by
  unfold prefTree
  rw [List.take_succ, he]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
  exact replay_snoc _ _ _

theorem kept_succ {t : Nat} {e : LogEntry} (he : log[t]? = some e) :
    replay (keptUpTo log S (t + 1)) T0 =
      if S t then e.op.apply (replay (keptUpTo log S t) T0) else replay (keptUpTo log S t) T0 := by
  unfold keptUpTo
  rw [List.range_succ, List.filterMap_append]
  by_cases h : S t
  · simp only [List.filterMap_cons, List.filterMap_nil, if_pos h, he, Option.map_some]
    exact replay_snoc _ _ _
  · simp only [List.filterMap_cons, List.filterMap_nil, if_neg h, List.append_nil]

/-- The entry `x` is in `S` and writes `(j, b)`. -/
def KW (x : Nat) (j : Ino) (b : GoString) : Prop := S x ∧ ∃ e, log[x]? = some e ∧ e.op.Writes j b

/-- The last kept writer of `(j, b)` below `t`. -/
def lastW (t : Nat) (j : Ino) (b : GoString) : Option Nat :=
  ((List.range t).filter (fun x => decide (S x ∧ ∃ e, log[x]? = some e ∧ e.op.Writes j b))).getLast?

theorem lastW_succ (t : Nat) (j : Ino) (b : GoString) :
    lastW log S (t + 1) j b = if KW log S t j b then some t else lastW log S t j b := by
  unfold lastW KW
  rw [List.range_succ, List.filter_append]
  by_cases h : S t ∧ ∃ e, log[t]? = some e ∧ e.op.Writes j b
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

theorem lastW_spec (j : Ino) (b : GoString) : ∀ t, match lastW log S t j b with
    | some w => w < t ∧ KW log S w j b ∧ ∀ y, w < y → y < t → ¬ KW log S y j b
    | none => ∀ y, y < t → ¬ KW log S y j b
  | 0 => by simp [lastW]
  | t + 1 => by
    have ih := lastW_spec j b t
    rw [lastW_succ]
    by_cases h : KW log S t j b
    · rw [if_pos h]; exact ⟨Nat.lt_succ_self _, h, fun y h1 h2 => by omega⟩
    · rw [if_neg h]
      revert ih
      cases lastW log S t j b with
      | some w =>
        rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun y hy1 hy2 => ?_⟩
        rcases Nat.lt_or_ge y t with hy | hy
        · exact h3 y hy1 hy
        · have : y = t := by omega
          subst this; exact h
      | none =>
        intro h3 y hy
        rcases Nat.lt_or_ge y t with hy' | hy'
        · exact h3 y hy'
        · have : y = t := by omega
          subst this; exact h

/-- A slot no entry of `[u, v)` writes holds at `v` what it held at `u`. -/
theorem prefTree_frame {j : Ino} {b : GoString} {u : Nat} :
    ∀ v, u ≤ v → v ≤ log.length →
      (∀ y (e : LogEntry), u ≤ y → y < v → log[y]? = some e → ¬ e.op.Writes j b) →
      (prefTree T0 log v).entry j b = (prefTree T0 log u).entry j b
  | 0, huv, _, _ => by rw [show u = 0 by omega]
  | v + 1, huv, hv, hw => by
    rcases Nat.lt_or_ge v u with h | h
    · rw [show u = v + 1 by omega]
    obtain ⟨e, he⟩ : ∃ e, log[v]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [prefTree_succ T0 log he, apply_other _ _ _ _ (hw v e h (Nat.lt_succ_self _) he)]
    exact prefTree_frame v h (by omega) (fun y e' h1 h2 h3 => hw y e' h1 (by omega) h3)

/-- What a slot holds in the replay of the kept entries below `t`. -/
def slotV (t : Nat) (j : Ino) (b : GoString) : Option Node :=
  match lastW log S t j b with
  | some w => (prefTree T0 log (w + 1)).entry j b
  | none => T0.entry j b

end run

section cut
variable {T0 : Tree} {log : List LogEntry} {S : Nat → Prop}

/-- An earlier writer of a slot a kept entry writes is kept. -/
theorem kept_writer (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hc : Closed log S) {x y : Nat}
    {ex ey : LogEntry} (hx : log[x]? = some ex) (hy : log[y]? = some ey) (hSx : S x) (hyx : y < x)
    {sl : Slot} (hsl : sl ∈ ex.op.slots) (hw : ey.op.Writes sl.1 sl.2) : S y := by
  refine hc x y hSx ⟨hyx, ex, hx, ?_⟩
  rcases hw with h | ⟨j0, b0, h⟩
  · exact hps x y ex ey hyx hx hy ⟨sl, hsl, h⟩
  · exact (hdx y ey hy (by rw [h]; trivial)).2 x ex hyx hx

/-- A kept entry's slots hold, in the replay of the kept entries before it, what they held in the
run when it took effect. -/
theorem kept_reads (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hc : Closed log S) {x : Nat}
    {ex : LogEntry} (hx : log[x]? = some ex) (hSx : S x)
    (hA : ∀ j b, (replay (keptUpTo log S x) T0).entry j b = slotV T0 log S x j b)
    (sl : Slot) (hsl : sl ∈ ex.op.slots) :
    (replay (keptUpTo log S x) T0).entry sl.1 sl.2 = (prefTree T0 log x).entry sl.1 sl.2 := by
  have hxL : x < log.length := (List.getElem?_eq_some_iff.1 hx).1
  rw [hA]
  unfold slotV
  have hsp := lastW_spec log S sl.1 sl.2 x
  -- no writer at all of the slot after the last kept one: each would be kept
  have hno : ∀ u, (∀ y, u ≤ y → y < x → ¬ KW log S y sl.1 sl.2) →
      ∀ y (e : LogEntry), u ≤ y → y < x → log[y]? = some e → ¬ e.op.Writes sl.1 sl.2 :=
    fun u hk y e h1 h2 he hw => hk y h1 h2 ⟨kept_writer hps hdx hc hx he hSx h2 hsl hw, e, he, hw⟩
  revert hsp
  cases lastW log S x sl.1 sl.2 with
  | some w =>
    rintro ⟨hw1, -, hw3⟩
    exact (prefTree_frame T0 log x (by omega) (by omega)
      (hno (w + 1) (fun y h1 h2 => hw3 y (by omega) h2))).symm
  | none =>
    intro hk
    rw [← prefTree_zero T0 log]
    exact (prefTree_frame T0 log x (Nat.zero_le _) (by omega)
      (hno 0 (fun y _ h2 => hk y h2))).symm

/-- **The slots of the replay** of the kept entries below `t`: as right after their last kept
writer. -/
theorem kept_entry (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hc : Closed log S) :
    ∀ t, t ≤ log.length → ∀ j b,
      (replay (keptUpTo log S t) T0).entry j b = slotV T0 log S t j b
  | 0, _, j, b => by simp [keptUpTo, replay, slotV, lastW]
  | t + 1, ht, j, b => by
    have ih := kept_entry hps hdx hc t (by omega)
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [kept_succ T0 log S he]
    unfold slotV
    rw [lastW_succ]
    by_cases hS : S t
    · rw [if_pos hS]
      by_cases hw : e.op.Writes j b
      · rw [if_pos ⟨hS, e, he, hw⟩]
        show _ = (prefTree T0 log (t + 1)).entry j b
        rw [prefTree_succ T0 log he]
        exact apply_agree _ _ _ (fun sl hsl => kept_reads hps hdx hc he hS ih sl hsl) j b hw
      · rw [if_neg (fun ⟨_, e', he', hw'⟩ => by rw [he] at he'; cases he'; exact hw hw'),
          apply_other _ _ _ _ hw, ih]; rfl
    · rw [if_neg hS, if_neg (fun h => hS h.1), ih]; rfl

end cut

end Fs
end Perennial

end
