/-
The proof of the consistent-cut theorem (`closed_cut`; the disciplines are in `TreeCut.lean`). Pure.
Untrusted.

The argument (`notes/wal-fsext-i2-design.md`, "Implementation log"):
1. *Slots.* By induction along the log, the replay of the kept entries holds in each slot what the
   run held right after the slot's last kept writer (`kept_entry`): a kept entry's slots held, in
   the replay, what they held in the run when it took effect, because every earlier writer of them
   is kept (`PerSlotSeq`, `DirOpExcl`, closure).
2. *Directories, per root.* For a root `r`, let `a r` be past the last kept directory operation of
   `r` and the last kept legacy entry. Every legacy entry and every entry of `r` below `a r` is kept
   (`DirOpExcl`), so up to `a r` the replay has the run's directories of `r` (`kept_keys_below`);
   after `a r` only file operations of `r` are kept, and the run has, from `a r` to past the last kept
   entry of `r`, only file operations of `r` and entries of other roots, which write no directory of
   `r` (`RootTags`). So the replay has `T (a r)`'s directories of `r` and their entries naming
   directories (`kept_keys_r`, `kept_slot_r`, `run_dirs_r`), and the roots' parts make a tree
   (`treeWf_merge`). Without a kept entry past the legacy prefix, the replay is a prefix's tree.
3. *Files.* A kept operation keeps the replay's files named once (a create's inode is new, a
   rename moves the one entry naming what it moves, a `mkdir` and a removal name no file).
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
variable {T0 : Tree} {log : List LogEntry} {S : Nat → Prop} {s0 : Nat} {ρ : Ino → GoString}
  {R : List (GoString × Ino)}

/-- An entry of the legacy prefix took effect before every later entry's call began. -/
theorem legacy_before (hdx : DirOpExcl ρ log s0) {y z : Nat} {ey ez : LogEntry}
    (hy : log[y]? = some ey) (hys : y < s0) (hyz : y < z) (hz : log[z]? = some ez) : y < ez.start :=
  ((hdx y ey hy).1 hys).2 z ez hyz hz

/-- A directory operation took effect before every later entry of its root began. -/
theorem dirOp_before (hdx : DirOpExcl ρ log s0) {y z : Nat} {ey ez : LogEntry}
    (hy : log[y]? = some ey) (hd : ey.op.IsDirOp) (hyz : y < z) (hz : log[z]? = some ez)
    (ht : tagOf ρ ez = tagOf ρ ey) : y < ez.start :=
  ((hdx y ey hy).2 hd).2 z ez hyz hz ht

/-- An entry from `s0` on writes only directories of its root. -/
theorem writer_tag (hρ : RootTags ρ R T0 log s0) {z : Nat} {ez : LogEntry} (hzs : s0 ≤ z)
    (hz : log[z]? = some ez) {j : Ino} {b : GoString} (hw : ez.op.Writes j b) : tagOf ρ ez = ρ j :=
  (hρ.ops z ez hzs hz j b hw).symm

/-- An earlier writer of a slot a kept entry writes is kept. -/
theorem kept_writer (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hc : Closed log S) {x y : Nat}
    {ex ey : LogEntry} (hx : log[x]? = some ex) (hy : log[y]? = some ey) (hSx : S x) (hyx : y < x)
    {sl : Slot} (hsl : sl ∈ ex.op.slots) (hw : ey.op.Writes sl.1 sl.2) : S y := by
  refine hc x y hSx ⟨hyx, ex, hx, ?_⟩
  rcases hw with h | ⟨j0, b0, h⟩
  · exact hps x y ex ey hyx hx hy ⟨sl, hsl, h⟩
  · rcases Nat.lt_or_ge y s0 with hys | hys
    · exact legacy_before hdx hy hys hyx hx
    · refine dirOp_before hdx hy (by rw [h]; trivial) hyx hx ?_
      rw [writer_tag hρ (by omega) hx (j := sl.1) (b := sl.2) (.inl hsl),
        writer_tag hρ hys hy (j := sl.1) (b := sl.2) (.inr ⟨j0, b0, h⟩)]

/-- A kept entry's slots hold, in the replay of the kept entries before it, what they held in the
run when it took effect. -/
theorem kept_reads (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0) (hc : Closed log S) {x : Nat}
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
    fun u hk y e h1 h2 he hw => hk y h1 h2 ⟨kept_writer hρ hps hdx hc hx he hSx h2 hsl hw, e, he, hw⟩
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
theorem kept_entry (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hc : Closed log S) :
    ∀ t, t ≤ log.length → ∀ j b,
      (replay (keptUpTo log S t) T0).entry j b = slotV T0 log S t j b
  | 0, _, j, b => by simp [keptUpTo, replay, slotV, lastW]
  | t + 1, ht, j, b => by
    have ih := kept_entry hρ hps hdx hc t (by omega)
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
        exact apply_agree _ _ _ (fun sl hsl => kept_reads hρ hps hdx hc he hS ih sl hsl) j b hw
      · rw [if_neg (fun ⟨_, e', he', hw'⟩ => by rw [he] at he'; cases he'; exact hw hw'),
          apply_other _ _ _ _ hw, ih]; rfl
    · rw [if_neg hS, if_neg (fun h => hS h.1), ih]; rfl

/-! ## File operations keep the directories -/

theorem fileOp_dirs {o : MetaOp} (hnd : ¬ o.IsDirOp) {m : Tree} (hok : OpOk m o) (j : Ino)
    (b : GoString) (J : Ino) :
    (o.apply m).entry j b = some (.dir J) ↔ m.entry j b = some (.dir J) := by
  cases o with
  | create j0 b0 i =>
    obtain ⟨-, hn⟩ := hok
    rw [entry_create]
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [hn]; simp
    · rfl
  | mkdir j0 b0 J0 => exact absurd trivial hnd
  | remove j0 b0 n =>
    obtain ⟨-, hn⟩ := hok
    rw [entry_remove]
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [hn]
      exact ⟨fun h => (nomatch h), fun h => absurd ⟨J, Option.some.inj h⟩ hnd⟩
    · rfl
  | rename j0 b0 j1 b1 n old =>
    obtain ⟨-, -, hn, ho⟩ := hok
    have hn' : ∀ J', n ≠ .dir J' := fun J' h => hnd (.inl ⟨J', h⟩)
    have ho' : ∀ J', old ≠ some (.dir J') := fun J' h => hnd (.inr ⟨J', h⟩)
    rw [entry_rename, hn]
    simp only
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [ho]
      exact ⟨fun h => absurd (Option.some.inj h) (hn' J), fun h => absurd h (ho' J)⟩
    · split
      · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [hn]
        exact ⟨fun h => (nomatch h), fun h => absurd (Option.some.inj h) (hn' J)⟩
      · rfl

theorem opOk_slots {o : MetaOp} (hnd : ¬ o.IsDirOp) {m : Tree} (hok : OpOk m o) :
    ∀ sl ∈ o.slots, sl.1 ∈ m := by
  cases o with
  | create j0 b0 i => intro sl hsl; simp [MetaOp.slots] at hsl; subst hsl; exact hok.1
  | mkdir => exact absurd trivial hnd
  | remove j0 b0 n => intro sl hsl; simp [MetaOp.slots] at hsl; subst hsl; exact hok.1
  | rename j0 b0 j1 b1 n old =>
    intro sl hsl; simp [MetaOp.slots] at hsl
    rcases hsl with rfl | rfl
    · exact hok.1
    · exact hok.2.1

theorem fileOp_mem {o : MetaOp} (hnd : ¬ o.IsDirOp) {m : Tree} (hd : ∀ sl ∈ o.slots, sl.1 ∈ m)
    (x : Ino) : x ∈ o.apply m ↔ x ∈ m := by
  cases o with
  | create j0 b0 i =>
    simp only [MetaOp.apply]; rw [mem_upd]
    have := hd (j0, b0) (by simp [MetaOp.slots])
    exact ⟨fun h => h.elim (fun h => h ▸ this) id, .inr⟩
  | mkdir => exact absurd trivial hnd
  | remove j0 b0 n =>
    simp only [MetaOp.apply]; rw [mem_upd]
    have := hd (j0, b0) (by simp [MetaOp.slots])
    exact ⟨fun h => h.elim (fun h => h ▸ this) id, .inr⟩
  | rename j0 b0 j1 b1 n old =>
    have h0 := hd (j0, b0) (by simp [MetaOp.slots])
    have h1 := hd (j1, b1) (by simp [MetaOp.slots])
    simp only [MetaOp.apply]
    split
    · rw [mem_upd, mem_upd]
      exact ⟨fun h => h.elim (fun h => h ▸ h1) (fun h => h.elim (fun h => h ▸ h0) id),
        fun h => .inr (.inr h)⟩
    · exact Iff.rfl

/-! ## Where the kept entries stop being a prefix -/

theorem exists_greatest (P : Nat → Prop) : ∀ n, (∃ x, x ≤ n ∧ P x) →
    ∃ g, g ≤ n ∧ P g ∧ ∀ x, x ≤ n → P x → x ≤ g
  | 0, ⟨x, hx, hp⟩ => ⟨0, Nat.le_refl _, by rw [show x = 0 by omega] at hp; exact hp,
      fun y hy _ => hy⟩
  | n + 1, ⟨x, hx, hp⟩ => by
    by_cases hn : P (n + 1)
    · exact ⟨n + 1, Nat.le_refl _, hn, fun y hy _ => hy⟩
    · have hxn : x ≤ n := by
        rcases Nat.lt_or_ge x (n + 1) with h | h
        · omega
        · rw [show x = n + 1 by omega] at hp; exact absurd hp hn
      obtain ⟨g, hg, hpg, hmax⟩ := exists_greatest P n ⟨x, hxn, hp⟩
      refine ⟨g, by omega, hpg, fun y hy hpy => hmax y ?_ hpy⟩
      rcases Nat.lt_or_ge y (n + 1) with h | h
      · omega
      · rw [show y = n + 1 by omega] at hpy; exact absurd hpy hn

/-- Below `a`, everything is kept: the replay is the run. -/
theorem kept_prefix {a : Nat} (ha : ∀ y, y < a → S y) :
    ∀ t, t ≤ a → t ≤ log.length → replay (keptUpTo log S t) T0 = prefTree T0 log t
  | 0, _, _ => by simp [keptUpTo, replay, prefTree]
  | t + 1, h1, h2 => by
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [kept_succ T0 log S he, if_pos (ha t (by omega)), prefTree_succ T0 log he,
      kept_prefix ha t (by omega) (by omega)]

/-- Some tree of the run, not later than `t`, has the replay's slot. -/
theorem kept_slot_le (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0) (hc : Closed log S) {t : Nat}
    (ht : t ≤ log.length) (j : Ino) (b : GoString) :
    ∃ g, g ≤ t ∧ (replay (keptUpTo log S t) T0).entry j b = (prefTree T0 log g).entry j b := by
  rw [kept_entry hρ hps hdx hc t ht]
  unfold slotV
  have hsp := lastW_spec log S j b t
  revert hsp
  cases lastW log S t j b with
  | some w => rintro ⟨hw1, -, -⟩; exact ⟨w + 1, by omega, rfl⟩
  | none => intro _; exact ⟨0, Nat.zero_le _, by rw [prefTree_zero]⟩

/-! ## Directories an operation adds -/

/-- A directory of a tree stays one after any operation. -/
theorem mem_apply_of_mem (o : MetaOp) (m : Tree) (x : Ino) (h : x ∈ m) : x ∈ o.apply m := by
  cases o with
  | create j b i => simp only [MetaOp.apply]; rw [mem_upd]; exact .inr h
  | mkdir j b J =>
    simp only [MetaOp.apply]
    rw [GMap.mem_iff]
    by_cases hx : J = x
    · subst hx; simp
    · rw [GMap.lookup_insert_ne _ _ hx, ← GMap.mem_iff, mem_upd]; exact .inr h
  | remove j b n => simp only [MetaOp.apply]; rw [mem_upd]; exact .inr h
  | rename j b j' b' n old =>
    simp only [MetaOp.apply]
    split
    · rw [mem_upd, mem_upd]; exact .inr (.inr h)
    · exact h

/-- An operation adds to a tree's directories only directories it writes. -/
theorem mem_apply_writes (o : MetaOp) (m : Tree) (x : Ino) (h : x ∈ o.apply m) :
    x ∈ m ∨ ∃ b, o.Writes x b := by
  cases o with
  | create j b i =>
    simp only [MetaOp.apply] at h; rw [mem_upd] at h
    rcases h with rfl | h
    · exact .inr ⟨b, .inl (by simp [MetaOp.slots])⟩
    · exact .inl h
  | mkdir j b J =>
    simp only [MetaOp.apply] at h
    rw [GMap.mem_iff] at h
    by_cases hx : J = x
    · subst hx; exact .inr ⟨b, .inr ⟨j, b, rfl⟩⟩
    · rw [GMap.lookup_insert_ne _ _ hx, ← GMap.mem_iff, mem_upd] at h
      rcases h with rfl | h
      · exact .inr ⟨b, .inl (by simp [MetaOp.slots])⟩
      · exact .inl h
  | remove j b n =>
    simp only [MetaOp.apply] at h; rw [mem_upd] at h
    rcases h with rfl | h
    · exact .inr ⟨b, .inl (by simp [MetaOp.slots])⟩
    · exact .inl h
  | rename j b j' b' n old =>
    simp only [MetaOp.apply] at h
    split at h
    · rw [mem_upd, mem_upd] at h
      rcases h with rfl | rfl | h
      · exact .inr ⟨b', .inl (by simp [MetaOp.slots])⟩
      · exact .inr ⟨b, .inl (by simp [MetaOp.slots])⟩
      · exact .inl h
    · exact .inl h

/-- An operation leaves a directory it does not write a directory or not. -/
theorem mem_apply_other (o : MetaOp) (m : Tree) (x : Ino) (h : ∀ b, ¬ o.Writes x b) :
    x ∈ o.apply m ↔ x ∈ m :=
  ⟨fun hx => (mem_apply_writes o m x hx).resolve_right (fun ⟨b, hb⟩ => h b hb), mem_apply_of_mem o m x⟩

/-- Whether an operation leaves `x` a directory depends only on whether it was one and on what the
operation's slots held. -/
theorem mem_apply_congr (o : MetaOp) (m1 m2 : Tree) (x : Ino) (hk : x ∈ m1 ↔ x ∈ m2)
    (hs : ∀ sl ∈ o.slots, m1.entry sl.1 sl.2 = m2.entry sl.1 sl.2) :
    x ∈ o.apply m1 ↔ x ∈ o.apply m2 := by
  cases o with
  | create j b i => simp only [MetaOp.apply, mem_upd, hk]
  | mkdir j b J =>
    simp only [MetaOp.apply]
    by_cases hx : J = x
    · subst hx; rw [GMap.mem_iff, GMap.mem_iff]; simp
    · rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_insert_ne _ _ hx, GMap.lookup_insert_ne _ _ hx,
        ← GMap.mem_iff, ← GMap.mem_iff]
      simp only [mem_upd, hk]
  | remove j b n => simp only [MetaOp.apply, mem_upd, hk]
  | rename j b j' b' n old =>
    have h0 := hs (j, b) (by simp [MetaOp.slots])
    simp only at h0
    simp only [MetaOp.apply]
    rw [h0]
    split
    · simp only [mem_upd, hk]
    · exact hk

/-- Reachability carries over from `m` to `m'` for the directories of one root, when `m'` has `m`'s
entries naming directories in that root's directories. -/
theorem reach_restrict {m m' : Tree} {r : GoString}
    (hents : ∀ j b J, m.entry j b = some (.dir J) → ρ J = ρ j)
    (hd : ∀ j b J, ρ j = r → m.entry j b = some (.dir J) → m'.entry j b = some (.dir J)) :
    ∀ {x}, Reach R m x → ρ x = r → Reach R m' x := by
  intro x hx
  induction hx with
  | root r' j h => intro _; exact .root r' j h
  | child j b j' _ he ih =>
    intro hr
    have hj : ρ j = r := (hents j b j' he).symm.trans hr
    exact .child j b j' (ih hj) (hd j b j' hj he)

/-- **A tree made of the roots' parts of trees**: if each directory of `K` and its entries naming
directories are those of the tree `m r` of its root `r`, each `m r` a tree in which a directory named
by an entry is in its parent's root, a directory of `K` empty when it is a removed one of its tree,
and `K`'s names valid and its files named once, then `K` is a tree. -/
theorem treeWf_merge {K : Tree} {m : GoString → Tree}
    (hw : ∀ r, TreeWf R (m r))
    (hents : ∀ r j b J, (m r).entry j b = some (.dir J) → ρ J = ρ j)
    (hk : ∀ x, x ∈ K ↔ x ∈ m (ρ x))
    (hd : ∀ j b J, K.entry j b = some (.dir J) ↔ (m (ρ j)).entry j b = some (.dir J))
    (hempty : ∀ x, ¬ Reach R (m (ρ x)) x → (∀ b, (m (ρ x)).entry x b = none) →
      ∀ b, K.entry x b = none)
    (hn : ∀ j b n, K.entry j b = some n → NameOk b)
    (hu : ∀ j1 b1 j2 b2 i, K.entry j1 b1 = some (.file i) → K.entry j2 b2 = some (.file i) →
      j1 = j2 ∧ b1 = b2) :
    TreeWf R K := by
  have hKents : ∀ j b J, K.entry j b = some (.dir J) → ρ J = ρ j :=
    fun j b J h => hents _ j b J ((hd j b J).1 h)
  have hto : ∀ x, Reach R K x → Reach R (m (ρ x)) x := by
    intro x hx
    induction hx with
    | root r j h => exact .root r j h
    | child j b j' _ he ih =>
      rw [hKents j b j' he]; exact .child j b j' ih ((hd j b j').1 he)
  have hfrom : ∀ x, Reach R (m (ρ x)) x → Reach R K x := fun x hx =>
    reach_restrict (r := ρ x) (hents (ρ x)) (fun j b J hj h => (hd j b J).2 (by rw [hj]; exact h)) hx rfl
  refine ⟨fun x hx => (hk x).2 ((hw _).1 x (hto x hx)), fun x hx => ?_, fun j b n he => ⟨hn j b n he, ?_⟩,
    fun j b j' he => (hw _).2.2.2.1 j b j' ((hd j b j').1 he), fun j1 b1 j2 b2 n h1 h2 => ?_⟩
  · by_cases hr : Reach R (m (ρ x)) x
    · exact .inl (hfrom x hr)
    · rcases (hw (ρ x)).2.1 x ((hk x).1 hx) with h | ⟨he, hnn⟩
      · exact absurd h hr
      · refine .inr ⟨hempty x hr he, fun j0 b h0 => hnn j0 b ?_⟩
        have h1 := (hd j0 b x).1 h0
        rw [hKents j0 b x h0]; exact h1
  · intro j' hj'
    cases n with
    | file i => simp [Node.dirIno] at hj'
    | dir J =>
      simp only [Node.dirIno, List.mem_singleton] at hj'; subst hj'
      have h1 := ((hw (ρ j)).2.2.1 j b (.dir j') ((hd j b j').1 he)).2 j' (by simp [Node.dirIno])
      rw [← hKents j b j' he] at h1
      exact (hk j').2 h1
  · cases n with
    | file i => exact hu j1 b1 j2 b2 i h1 h2
    | dir J =>
      have g1 := (hd j1 b1 J).1 h1
      have g2 := (hd j2 b2 J).1 h2
      rw [← hKents j1 b1 J h1] at g1
      rw [← hKents j2 b2 J h2] at g2
      exact (hw (ρ J)).2.2.2.2 j1 b1 j2 b2 _ g1 g2

/-! ## Each root's cut -/

/-- The entries below `s0` and the directory operations of the root `r`, kept. -/
def DR (ρ : Ino → GoString) (log : List LogEntry) (S : Nat → Prop) (s0 : Nat) (r : GoString) (x : Nat) :
    Prop :=
  x < log.length ∧ S x ∧ ∃ e, log[x]? = some e ∧ (x < s0 ∨ (e.op.IsDirOp ∧ tagOf ρ e = r))

/-- **The cut of the root `r`**: some `a` past every kept legacy entry and kept directory operation of
`r`; every legacy entry and every entry of `r` below it kept; from it to any kept entry of `r`, no
legacy entry, and of `r`'s entries only file operations. -/
theorem cut_base_r (hdx : DirOpExcl ρ log s0) (hc : Closed log S) (hS : ∀ x, S x → x < log.length)
    (r : GoString) :
    ∃ a, a ≤ log.length ∧ (∀ y, DR ρ log S s0 r y → y < a) ∧
      (∀ y (ey : LogEntry), y < a → log[y]? = some ey → (y < s0 ∨ tagOf ρ ey = r) → S y) ∧
      ∀ z x (ez ex : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → log[x]? = some ex →
        tagOf ρ ex = r → s0 ≤ z ∧ (tagOf ρ ez = r → ¬ ez.op.IsDirOp) := by
  have hkeep : ∀ z x (ez ex : LogEntry), z ≤ x → S x → log[z]? = some ez → log[x]? = some ex →
      tagOf ρ ex = r → (z < s0 ∨ (ez.op.IsDirOp ∧ tagOf ρ ez = r)) → DR ρ log S s0 r z := by
    intro z x ez ex hzx hSx hz hx htx hd
    refine ⟨(List.getElem?_eq_some_iff.1 hz).1, ?_, ez, hz, hd⟩
    rcases Nat.lt_or_ge z x with h | h
    · refine hc x z hSx ⟨h, ex, hx, ?_⟩
      rcases hd with hd | ⟨hd, htz⟩
      · exact legacy_before hdx hz hd h hx
      · exact dirOp_before hdx hz hd h hx (htx.trans htz.symm)
    · rw [show z = x by omega]; exact hSx
  have hpost : ∀ a, (∀ y, DR ρ log S s0 r y → y < a) →
      ∀ z x (ez ex : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → log[x]? = some ex →
        tagOf ρ ex = r → s0 ≤ z ∧ (tagOf ρ ez = r → ¬ ez.op.IsDirOp) := by
    intro a ha z x ez ex h1 h2 hSx hz hx htx
    refine ⟨Nat.le_of_not_lt fun hzs => ?_, fun htz hd => ?_⟩
    · have := ha z (hkeep z x ez ex h2 hSx hz hx htx (.inl hzs)); omega
    · have := ha z (hkeep z x ez ex h2 hSx hz hx htx (.inr ⟨hd, htz⟩)); omega
  by_cases hex : ∃ x, x ≤ log.length ∧ DR ρ log S s0 r x
  · obtain ⟨x0, hx0, hD0⟩ := hex
    obtain ⟨g, -, hg, hmax⟩ := exists_greatest (DR ρ log S s0 r) log.length ⟨x0, hx0, hD0⟩
    have hlt : ∀ y, DR ρ log S s0 r y → y < g + 1 :=
      fun y hy => Nat.lt_succ_of_le (hmax y (Nat.le_of_lt hy.1) hy)
    refine ⟨g + 1, hg.1, hlt, fun y ey hy hey hyr => ?_, hpost (g + 1) hlt⟩
    obtain ⟨-, hSg, eg, heg, hdg⟩ := hg
    rcases Nat.lt_or_ge y g with h | h
    · refine hc g y hSg ⟨h, eg, heg, ?_⟩
      rcases hdg with hgs | ⟨hgd, hgr⟩
      · rw [((hdx g eg heg).1 hgs).1]; exact h
      · rcases hyr with hys | hyr
        · exact legacy_before hdx hey hys h heg
        · exact Nat.lt_of_not_le fun hle =>
            ((hdx g eg heg).2 hgd).1 y ey hle h hey (hyr.trans hgr.symm)
    · rw [show y = g by omega]; exact hSg
  · have hlt : ∀ y, DR ρ log S s0 r y → y < 0 :=
      fun y hy => absurd ⟨y, Nat.le_of_lt hy.1, hy⟩ hex
    exact ⟨0, Nat.zero_le _, hlt, fun y _ hy => absurd hy (Nat.not_lt_zero _), hpost 0 hlt⟩

/-- From the cut of `r` on, a run of file operations of `r` and of entries of other roots keeps the
entries naming directories in `r`'s directories, and `r`'s directories. -/
theorem run_dirs_r (hρ : RootTags ρ R T0 log s0) (hv : LogValid T0 log s0) {r : GoString} {a : Nat} :
    ∀ u, a ≤ u → u ≤ log.length →
      (∀ z (ez : LogEntry), a ≤ z → z < u → log[z]? = some ez →
        s0 ≤ z ∧ (tagOf ρ ez = r → ¬ ez.op.IsDirOp)) →
      (∀ j b J, ρ j = r → ((prefTree T0 log u).entry j b = some (.dir J) ↔
        (prefTree T0 log a).entry j b = some (.dir J))) ∧
      (∀ x, ρ x = r → (x ∈ prefTree T0 log u ↔ x ∈ prefTree T0 log a))
  | 0, hau, _, _ => by
    rw [show a = 0 by omega]; exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  | u + 1, hau, hu, hf => by
    rcases Nat.lt_or_ge u a with h | h
    · rw [show a = u + 1 by omega]; exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    obtain ⟨e, he⟩ : ∃ e, log[u]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hus, hnd⟩ := hf u e h (Nat.lt_succ_self _) he
    obtain ⟨ih1, ih2⟩ := run_dirs_r hρ hv u h (by omega)
      (fun z ez h1 h2 hz => hf z ez h1 (by omega) hz)
    rw [prefTree_succ T0 log he]
    by_cases ht : tagOf ρ e = r
    · have hnd' := hnd ht
      have hok := (hv u e he (fun h' => h'.elim hnd' (fun hlt => by omega))).1
      exact ⟨fun j b J hj => (fileOp_dirs hnd' hok j b J).trans (ih1 j b J hj),
        fun x hx => (fileOp_mem hnd' (opOk_slots hnd' hok) x).trans (ih2 x hx)⟩
    · have hnw : ∀ x b, ρ x = r → ¬ e.op.Writes x b := fun x b hx hw =>
        ht ((writer_tag hρ hus he hw).trans hx)
      exact ⟨fun j b J hj => by rw [apply_other _ _ _ _ (hnw j b hj)]; exact ih1 j b J hj,
        fun x hx => (mem_apply_other _ _ _ (fun b => hnw x b hx)).trans (ih2 x hx)⟩

/-- The replay's slot in a directory of `r`, as some tree of the run from `r`'s cut on (with, from
the cut to it, no legacy entry and only file operations of `r`) has it. -/
theorem kept_slot_r (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hc : Closed log S) {r : GoString} {a : Nat} (haL : a ≤ log.length) (has : s0 ≤ a)
    (ha : ∀ y (ey : LogEntry), y < a → log[y]? = some ey → (y < s0 ∨ tagOf ρ ey = r) → S y)
    (hb : ∀ z x (ez ex : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → log[x]? = some ex →
      tagOf ρ ex = r → s0 ≤ z ∧ (tagOf ρ ez = r → ¬ ez.op.IsDirOp))
    (j : Ino) (b : GoString) (hj : ρ j = r) :
    ∃ g, a ≤ g ∧ g ≤ log.length ∧
      (∀ z (ez : LogEntry), a ≤ z → z < g → log[z]? = some ez →
        s0 ≤ z ∧ (tagOf ρ ez = r → ¬ ez.op.IsDirOp)) ∧
      (replay (keptUpTo log S log.length) T0).entry j b = (prefTree T0 log g).entry j b := by
  rw [kept_entry hρ hps hdx hc log.length (Nat.le_refl _)]
  unfold slotV
  have hsp := lastW_spec log S j b log.length
  have hkw : ∀ y (e : LogEntry), y < a → log[y]? = some e → e.op.Writes j b → KW log S y j b := by
    intro y e hy he hw
    refine ⟨ha y e hy he ?_, e, he, hw⟩
    rcases Nat.lt_or_ge y s0 with h | h
    · exact .inl h
    · exact .inr ((writer_tag hρ h he hw).trans hj)
  have hfr : ∀ u, u ≤ a → (∀ y, u ≤ y → y < log.length → ¬ KW log S y j b) →
      (prefTree T0 log a).entry j b = (prefTree T0 log u).entry j b := fun u hu hk =>
    prefTree_frame T0 log a hu haL (fun y e h1 h2 he hw => hk y h1 (by omega) (hkw y e h2 he hw))
  revert hsp
  cases lastW log S log.length j b with
  | some w =>
    rintro ⟨hw1, hw2, hw3⟩
    rcases Nat.lt_or_ge w a with h | h
    · refine ⟨a, Nat.le_refl _, haL, fun z ez h1 h2 => absurd h2 (by omega), ?_⟩
      exact (hfr (w + 1) (by omega) (fun y h1 h2 => hw3 y (by omega) h2)).symm
    · obtain ⟨hSw, ew, hew, hww⟩ := hw2
      have htw : tagOf ρ ew = r := (writer_tag hρ (by omega) hew hww).trans hj
      exact ⟨w + 1, by omega, by omega,
        fun z ez h1 h2 hz => hb z w ez ew h1 (by omega) hSw hz hew htw, rfl⟩
  | none =>
    intro hk
    refine ⟨a, Nat.le_refl _, haL, fun z ez h1 h2 => absurd h2 (by omega), ?_⟩
    rw [hfr 0 (Nat.zero_le _) (fun y _ h2 => hk y h2), prefTree_zero]

/-- Up to `r`'s cut, the replay has the run's directories of `r` (every legacy entry kept). -/
theorem kept_keys_below (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hc : Closed log S) {r : GoString} {a : Nat} (haL : a ≤ log.length)
    (hlegacy : ∀ y, y < s0 → S y)
    (ha : ∀ y (ey : LogEntry), y < a → log[y]? = some ey → (y < s0 ∨ tagOf ρ ey = r) → S y) :
    ∀ t, s0 ≤ t → t ≤ a → ∀ x, ρ x = r →
      (x ∈ replay (keptUpTo log S t) T0 ↔ x ∈ prefTree T0 log t)
  | 0, hst, _, x, _ => by rw [kept_prefix hlegacy 0 (by omega) (by omega)]
  | t + 1, hst, hta, x, hx => by
    rcases Nat.lt_or_ge t s0 with h | h
    · rw [kept_prefix hlegacy (t + 1) (by omega) (by omega)]
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ih := kept_keys_below hρ hps hdx hc haL hlegacy ha t h (by omega) x hx
    rw [kept_succ T0 log S he, prefTree_succ T0 log he]
    by_cases ht : tagOf ρ e = r
    · have hSt := ha t e (by omega) he (.inr ht)
      rw [if_pos hSt]
      have hA := kept_entry hρ hps hdx hc (T0 := T0) t (by omega)
      exact mem_apply_congr _ _ _ x ih (fun sl hsl => kept_reads hρ hps hdx hc he hSt hA sl hsl)
    · have hnw : ∀ b, ¬ e.op.Writes x b := fun b hw => ht ((writer_tag hρ h he hw).trans hx)
      rw [mem_apply_other _ _ _ hnw]
      by_cases hS : S t
      · rw [if_pos hS, mem_apply_other _ _ _ hnw]; exact ih
      · rw [if_neg hS]; exact ih

/-- From `r`'s cut on, the replay has the directories of `r` of the run's tree at the cut. -/
theorem kept_keys_r (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hv : LogValid T0 log s0) (hc : Closed log S) {r : GoString} {a : Nat} (haL : a ≤ log.length)
    (has : s0 ≤ a) (hlegacy : ∀ y, y < s0 → S y)
    (ha : ∀ y (ey : LogEntry), y < a → log[y]? = some ey → (y < s0 ∨ tagOf ρ ey = r) → S y)
    (hb : ∀ z x (ez ex : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → log[x]? = some ex →
      tagOf ρ ex = r → s0 ≤ z ∧ (tagOf ρ ez = r → ¬ ez.op.IsDirOp)) :
    ∀ t, a ≤ t → t ≤ log.length → ∀ x, ρ x = r →
      (x ∈ replay (keptUpTo log S t) T0 ↔ x ∈ prefTree T0 log a)
  | 0, hat, hL, x, hx => by
    have h0 : a = 0 := by omega
    subst h0
    exact kept_keys_below hρ hps hdx hc haL hlegacy ha 0 has (Nat.le_refl _) x hx
  | t + 1, hat, hL, x, hx => by
    rcases Nat.lt_or_ge t a with h | h
    · have h0 : a = t + 1 := by omega
      subst h0
      exact kept_keys_below hρ hps hdx hc haL hlegacy ha (t + 1) has (Nat.le_refl _) x hx
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ih := kept_keys_r hρ hps hdx hv hc haL has hlegacy ha hb t h (by omega)
    rw [kept_succ T0 log S he]
    by_cases hS : S t
    · rw [if_pos hS]
      by_cases ht : tagOf ρ e = r
      · obtain ⟨hts, hnd⟩ := hb t t e e h (Nat.le_refl _) hS he he ht
        have hnd' := hnd ht
        have hok := (hv t e he (fun h' => h'.elim hnd' (fun hlt => by omega))).1
        have hrd := (run_dirs_r hρ hv t h (by omega)
          (fun z ez h1 h2 hz => hb z t ez e h1 (by omega) hS hz he ht)).2
        have hsr : ∀ sl ∈ e.op.slots, ρ sl.1 = r :=
          fun sl hsl => (writer_tag hρ hts he (j := sl.1) (b := sl.2) (.inl hsl)).symm.trans ht
        rw [fileOp_mem hnd' (fun sl hsl => (ih sl.1 (hsr sl hsl)).2
          ((hrd sl.1 (hsr sl hsl)).1 (opOk_slots hnd' hok sl hsl))) x]
        exact ih x hx
      · have hnw : ∀ b, ¬ e.op.Writes x b := fun b hw =>
          ht ((writer_tag hρ (by omega) he hw).trans hx)
        rw [mem_apply_other _ _ _ hnw]; exact ih x hx
    · rw [if_neg hS]; exact ih x hx

/-- Past the last kept entry, the replay is unchanged. -/
theorem kept_stop {a : Nat} (hb : ∀ y, a ≤ y → ¬ S y) :
    ∀ t, a ≤ t → t ≤ log.length → replay (keptUpTo log S t) T0 = replay (keptUpTo log S a) T0
  | 0, h, _ => by rw [show a = 0 by omega]
  | t + 1, h, hL => by
    rcases Nat.lt_or_ge t a with h' | h'
    · rw [show a = t + 1 by omega]
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [kept_succ T0 log S he, if_neg (hb t h')]
    exact kept_stop hb t h' (by omega)

/-- With every legacy entry kept, the replay names each file once. -/
theorem kept_inj (hρ : RootTags ρ R T0 log s0) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hv : LogValid T0 log s0) (hwf : ∀ t, t ≤ log.length → TreeWf R (prefTree T0 log t))
    (hc : Closed log S) (hlegacy : ∀ y, y < s0 → S y) :
    ∀ t, t ≤ log.length → ∀ j1 b1 j2 b2 i,
      (replay (keptUpTo log S t) T0).entry j1 b1 = some (.file i) →
      (replay (keptUpTo log S t) T0).entry j2 b2 = some (.file i) → j1 = j2 ∧ b1 = b2
  | 0, hL => by
    rw [kept_prefix hlegacy 0 (Nat.zero_le _) hL]
    exact fun j1 b1 j2 b2 _ h1 h2 => (hwf 0 hL).2.2.2.2 j1 b1 j2 b2 _ h1 h2
  | t + 1, hL => by
    rcases Nat.lt_or_ge t s0 with h | h
    · rw [kept_prefix hlegacy (t + 1) (by omega) hL]
      exact fun j1 b1 j2 b2 _ h1 h2 => (hwf (t + 1) hL).2.2.2.2 j1 b1 j2 b2 _ h1 h2
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ih := kept_inj hρ hps hdx hv hwf hc hlegacy t (by omega)
    rw [kept_succ T0 log S he]
    by_cases hS : S t
    · rw [if_pos hS]
      have hfresh : ∀ j0 b0 i0, e.op = .create j0 b0 i0 → ∀ j b,
          (replay (keptUpTo log S t) T0).entry j b ≠ some (.file i0) := by
        intro j0 b0 i0 hop j b hjb
        have hval := hv t e he (fun h' => h'.elim (fun hd => by rw [hop] at hd; exact hd)
          (fun hlt => by omega))
        obtain ⟨g, hg, hgeq⟩ := kept_slot_le (T0 := T0) hρ hps hdx hc (t := t) (by omega) j b
        exact hval.2 j0 b0 i0 hop g hg ⟨j, b, hgeq ▸ hjb⟩
      revert hfresh
      generalize replay (keptUpTo log S t) T0 = K at ih ⊢
      intro hfresh
      cases hop : e.op with
      | create j0 b0 i0 =>
        have fresh := hfresh j0 b0 i0 hop
        intro j1 b1 j2 b2 i h1 h2
        rw [entry_create] at h1 h2
        by_cases p1 : j0 = j1 ∧ b0 = b1 <;> by_cases p2 : j0 = j2 ∧ b0 = b2
        · exact ⟨p1.1.symm.trans p2.1, p1.2.symm.trans p2.2⟩
        · rw [if_pos p1] at h1; rw [if_neg p2] at h2
          cases (Option.some.inj h1); exact absurd h2 (fresh _ _)
        · rw [if_neg p1] at h1; rw [if_pos p2] at h2
          cases (Option.some.inj h2); exact absurd h1 (fresh _ _)
        · rw [if_neg p1] at h1; rw [if_neg p2] at h2; exact ih _ _ _ _ _ h1 h2
      | remove j0 b0 n =>
        intro j1 b1 j2 b2 i h1 h2
        rw [entry_remove] at h1 h2
        split at h1
        · exact nomatch h1
        split at h2
        · exact nomatch h2
        exact ih _ _ _ _ _ h1 h2
      | mkdir j0 b0 J =>
        intro j1 b1 j2 b2 i h1 h2
        rw [entry_mkdir] at h1 h2
        split at h1
        · simp at h1
        split at h1
        · simp at h1
        split at h2
        · simp at h2
        split at h2
        · simp at h2
        exact ih _ _ _ _ _ h1 h2
      | rename j0 b0 j1' b1' n old =>
        intro j1 b1 j2 b2 i h1 h2
        rw [entry_rename] at h1 h2
        cases hr : K.entry j0 b0 with
        | none => rw [hr] at h1 h2; exact ih _ _ _ _ _ h1 h2
        | some n' =>
          rw [hr] at h1 h2
          simp only at h1 h2
          by_cases p1 : j1' = j1 ∧ b1' = b1 <;> by_cases p2 : j1' = j2 ∧ b1' = b2
          · exact ⟨p1.1.symm.trans p2.1, p1.2.symm.trans p2.2⟩
          · rw [if_pos p1] at h1; rw [if_neg p2] at h2
            split at h2
            · exact nomatch h2
            · rename_i q2
              have := ih j0 b0 j2 b2 i (h1 ▸ hr) h2
              exact absurd this q2
          · rw [if_neg p1] at h1; rw [if_pos p2] at h2
            split at h1
            · exact nomatch h1
            · rename_i q1
              have := ih j0 b0 j1 b1 i (h2 ▸ hr) h1
              exact absurd this q1
          · rw [if_neg p1] at h1; rw [if_neg p2] at h2
            split at h1
            · exact nomatch h1
            split at h2
            · exact nomatch h2
            exact ih _ _ _ _ _ h1 h2
    · rw [if_neg hS]; exact ih

/-- **The consistent-cut theorem** (`TreeCut.lean` states the disciplines): the replay of a closed
set is a tree, each slot as right after its last kept writer, each file named in some tree of the
run, and each directory one of some tree of the run (each root's part of the replay is that of one
tree of the run: `kept_keys_r`, `kept_slot_r`). -/
theorem closed_cut
    (_hst : Starts log) (hps : PerSlotSeq log) (hdx : DirOpExcl ρ log s0)
    (hρ : RootTags ρ R T0 log s0) (hv : LogValid T0 log s0)
    (hwf : ∀ t, t ≤ log.length → TreeWf R (prefTree T0 log t))
    (hS : ∀ x, S x → x < log.length) (hc : Closed log S) :
    TreeWf R (replay (keptOps log S) T0) ∧
    (∀ j b, (replay (keptOps log S) T0).entry j b = slotAfter T0 log S j b) ∧
    (∀ i, Named (replay (keptOps log S) T0) i → ∃ t, t ≤ log.length ∧ Named (prefTree T0 log t) i) ∧
    (∀ j, j ∈ replay (keptOps log S) T0 → ∃ t, t ≤ log.length ∧ j ∈ prefTree T0 log t) := by
  have hK : keptOps log S = keptUpTo log S log.length := rfl
  rw [hK]
  have hslots : ∀ j b, (replay (keptUpTo log S log.length) T0).entry j b = slotAfter T0 log S j b :=
    fun j b => kept_entry hρ hps hdx hc log.length (Nat.le_refl _) j b
  have hnamed : ∀ i, Named (replay (keptUpTo log S log.length) T0) i →
      ∃ t, t ≤ log.length ∧ Named (prefTree T0 log t) i := by
    rintro i ⟨j, b, h⟩
    obtain ⟨g, hg, heq⟩ := kept_slot_le (T0 := T0) hρ hps hdx hc (t := log.length) (Nat.le_refl _) j b
    exact ⟨g, hg, j, b, heq ▸ h⟩
  by_cases hk : ∃ x, S x ∧ s0 ≤ x
  · obtain ⟨x0, hSx0, hx0⟩ := hk
    have hx0L := hS x0 hSx0
    have hlegacy : ∀ y, y < s0 → S y := fun y hy => by
      obtain ⟨e0, he0⟩ : ∃ e, log[x0]? = some e := ⟨_, List.getElem?_eq_getElem hx0L⟩
      obtain ⟨ey, hey⟩ : ∃ e, log[y]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact hc x0 y hSx0 ⟨by omega, e0, he0, legacy_before hdx hey hy (by omega) he0⟩
    have hcb := fun r => cut_base_r hdx hc hS r
    let a : GoString → Nat := fun r => Classical.choose (hcb r)
    have hspec := fun r => Classical.choose_spec (hcb r)
    have haL : ∀ r, a r ≤ log.length := fun r => (hspec r).1
    have has : ∀ r, s0 ≤ a r := fun r => by
      rcases Nat.eq_zero_or_pos s0 with h0 | h0
      · omega
      · obtain ⟨e, he⟩ : ∃ e, log[s0 - 1]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have : s0 - 1 < a r := (hspec r).2.1 (s0 - 1) ⟨by omega, hlegacy _ (by omega), e, he, .inl (by omega)⟩
        omega
    have hkeys : ∀ x, x ∈ replay (keptUpTo log S log.length) T0 ↔ x ∈ prefTree T0 log (a (ρ x)) :=
      fun x => kept_keys_r hρ hps hdx hv hc (haL (ρ x)) (has (ρ x)) hlegacy (hspec (ρ x)).2.2.1
        (hspec (ρ x)).2.2.2 log.length (haL _) (Nat.le_refl _) x rfl
    have hslot := fun j b => kept_slot_r (T0 := T0) hρ hps hdx hc (haL (ρ j)) (has (ρ j))
      (hspec (ρ j)).2.2.1 (hspec (ρ j)).2.2.2 j b rfl
    refine ⟨treeWf_merge (m := fun r => prefTree T0 log (a r)) (fun r => hwf _ (haL r))
      (fun r => hρ.ents (a r) (has r) (haL r)) hkeys (fun j b J => ?_) (fun x hx he b => ?_)
      (fun j b n he => ?_) (kept_inj hρ hps hdx hv hwf hc hlegacy log.length (Nat.le_refl _)),
      hslots, hnamed, fun j hj => ⟨a (ρ j), haL _, (hkeys j).1 hj⟩⟩
    · obtain ⟨g, hg1, hg2, hgw, heq⟩ := hslot j b
      rw [heq]; exact (run_dirs_r hρ hv g hg1 hg2 hgw).1 j b J rfl
    · obtain ⟨g, hg1, hg2, hgw, heq⟩ := hslot x b
      rw [heq]
      have hd := (run_dirs_r hρ hv g hg1 hg2 hgw).1
      by_cases hxg : x ∈ prefTree T0 log g
      · rcases (hwf g hg2).2.1 x hxg with hr | ⟨he', -⟩
        · exact absurd (reach_restrict (hρ.ents g (by have := has (ρ x); omega) hg2)
            (fun j b J hj h => (hd j b J hj).1 h) hr rfl) hx
        · exact he' b
      · have h0 : (prefTree T0 log g) !! x = none := by
          cases h : (prefTree T0 log g) !! x with
          | none => rfl
          | some _ => exact absurd (by rw [GMap.mem_iff, h]; rfl) hxg
        simp [Tree.entry, h0]
    · obtain ⟨g, hg, heq⟩ := kept_slot_le (T0 := T0) hρ hps hdx hc (t := log.length) (Nat.le_refl _) j b
      rw [heq] at he; exact ((hwf g hg).2.2.1 j b n he).1
  · have hk' : ∀ x, S x → x < s0 := fun x hx => Nat.lt_of_not_le fun h => hk ⟨x, hx, h⟩
    have hpre : ∃ a, a ≤ log.length ∧ (∀ y, y < a → S y) ∧ ∀ y, a ≤ y → ¬ S y := by
      by_cases hex : ∃ x, x ≤ log.length ∧ S x
      · obtain ⟨g, -, hg, hmax⟩ := exists_greatest S log.length hex
        have hgL := hS g hg
        refine ⟨g + 1, hgL, fun y hy => ?_, fun y hy hSy => ?_⟩
        · rcases Nat.lt_or_ge y g with h | h
          · obtain ⟨eg, heg⟩ : ∃ e, log[g]? = some e := ⟨_, List.getElem?_eq_getElem hgL⟩
            exact hc g y hg ⟨h, eg, heg, by rw [((hdx g eg heg).1 (hk' g hg)).1]; exact h⟩
          · rw [show y = g by omega]; exact hg
        · have := hmax y (Nat.le_of_lt (hS y hSy)) hSy; omega
      · exact ⟨0, Nat.zero_le _, fun y hy => absurd hy (Nat.not_lt_zero _),
          fun y _ hSy => hex ⟨y, Nat.le_of_lt (hS y hSy), hSy⟩⟩
    obtain ⟨a, haL, ha, hb⟩ := hpre
    have hKa : replay (keptUpTo log S log.length) T0 = prefTree T0 log a := by
      rw [kept_stop hb log.length haL (Nat.le_refl _), kept_prefix ha a (Nat.le_refl _) haL]
    refine ⟨?_, hslots, hnamed, fun j hj => ⟨a, haL, ?_⟩⟩
    · rw [hKa]; exact hwf a haL
    · rw [hKa] at hj; exact hj

end cut

/-! ## The roots' tags of a tree -/

theorem fst_eq_of_snd_nodup : ∀ {R : List (GoString × Ino)}, (R.map (·.2)).Nodup →
    ∀ {r r' : GoString} {i : Ino}, (r, i) ∈ R → (r', i) ∈ R → r = r'
  | [], _, _, _, _, h, _ => by simp at h
  | (a, b) :: R, hn, r, r', i, h1, h2 => by
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨rfl, h2'⟩ | h2
    · rfl
    · exact absurd (List.mem_map.2 ⟨(r', i), h2, rfl⟩) hn.1
    · subst h2'; exact absurd (List.mem_map.2 ⟨(r, i), h1, rfl⟩) hn.1
    · exact fst_eq_of_snd_nodup hn.2 h1 h2

theorem reach_of_reachFrom {R : List (GoString × Ino)} {m : Tree} {r : GoString} {ri : Ino}
    (hr : (r, ri) ∈ R) {j : Ino} (h : ReachFrom m ri j) : Reach R m j := by
  induction h with
  | root => exact .root r ri hr
  | child j b j' _ he ih => exact .child j b j' ih he

theorem reachFrom_of_reach {R : List (GoString × Ino)} {m : Tree} {j : Ino} (h : Reach R m j) :
    ∃ rj ∈ R, ReachFrom m rj.2 j := by
  induction h with
  | root r j hr => exact ⟨(r, j), hr, .root⟩
  | child j b j' _ he ih =>
    obtain ⟨rj, hrj, h⟩ := ih
    exact ⟨rj, hrj, .child j b j' h he⟩

/-- In a tree, a directory is reachable from one root only. -/
theorem reachFrom_unique {R : List (GoString × Ino)} {m : Tree} (hR : (R.map (·.2)).Nodup)
    (hw : TreeWf R m) {r : GoString} {ri : Ino} (hr : (r, ri) ∈ R) {j : Ino} (h : ReachFrom m ri j) :
    ∀ {r' : GoString} {ri' : Ino}, (r', ri') ∈ R → ReachFrom m ri' j → r = r' := by
  induction h with
  | root =>
    intro r' ri' hr' h'
    cases h' with
    | root => exact fst_eq_of_snd_nodup hR hr hr'
    | child j0 b _ _ he => exact absurd hr (hw.2.2.2.1 j0 b ri he r)
  | child j0 b j _ he ih =>
    intro r' ri' hr' h'
    cases h' with
    | root => exact absurd hr' (hw.2.2.2.1 j0 b _ he r')
    | child j0' b' _ h0' he' =>
      obtain ⟨rfl, rfl⟩ := hw.2.2.2.2 j0 b j0' b' _ he he'
      exact ih hr' h0'

/-- A tree's directories reachable from a root have that root's tag, under `ρ`, when `ρ` maps the
roots' directories to the roots and a directory named by an entry to its parent's root. -/
theorem rho_of_reachFrom {R : List (GoString × Ino)} {m : Tree} {ρ : Ino → GoString}
    (hroots : ∀ r j, (r, j) ∈ R → ρ j = r)
    (hents : ∀ j b J, m.entry j b = some (.dir J) → ρ J = ρ j) {r : GoString} {ri : Ino}
    (hr : (r, ri) ∈ R) {j : Ino} (h : ReachFrom m ri j) : ρ j = r := by
  induction h with
  | root => exact hroots r ri hr
  | child j b j' _ he ih => exact (hents j b j' he).trans ih

open Classical in
/-- **The roots' tags of a tree**: each directory reachable from a root mapped to that root. -/
theorem rootTags_exists {R : List (GoString × Ino)} {m : Tree} (hR : (R.map (·.2)).Nodup)
    (hw : TreeWf R m) :
    ∃ ρ : Ino → GoString, (∀ r j, (r, j) ∈ R → ρ j = r) ∧
      ∀ j b J, m.entry j b = some (.dir J) → ρ J = ρ j := by
  let ρ : Ino → GoString := fun j =>
    if h : ∃ rj ∈ R, ReachFrom m rj.2 j then (Classical.choose h).1 else []
  have hρ : ∀ r ri j, (r, ri) ∈ R → ReachFrom m ri j → ρ j = r := by
    intro r ri j hr h
    have hex : ∃ rj ∈ R, ReachFrom m rj.2 j := ⟨(r, ri), hr, h⟩
    have hs := Classical.choose_spec hex
    show (if h : ∃ rj ∈ R, ReachFrom m rj.2 j then (Classical.choose h).1 else []) = r
    rw [dif_pos hex]
    exact (reachFrom_unique hR hw hr h hs.1 hs.2).symm
  refine ⟨ρ, fun r j hr => hρ r j j hr .root, fun j b J he => ?_⟩
  have hj : j ∈ m := by
    cases h : m !! j with
    | none => simp [Tree.entry, h] at he
    | some _ => rw [GMap.mem_iff, h]; rfl
  rcases hw.2.1 j hj with hr | ⟨hemp, -⟩
  · obtain ⟨rj, hrj, h⟩ := reachFrom_of_reach hr
    rw [hρ rj.1 rj.2 J hrj (.child j b J h he), hρ rj.1 rj.2 j hrj h]
  · rw [hemp b] at he; cases he


end Fs
end Perennial

end
