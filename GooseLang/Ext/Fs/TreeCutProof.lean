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

/-- Some `a`: every entry below it kept; from it to any kept entry, only file operations. -/
theorem cut_base (hdx : DirOpExcl log) (hc : Closed log S) (hS : ∀ x, S x → x < log.length) :
    ∃ a, a ≤ log.length ∧ (∀ y, y < a → S y) ∧
      ∀ z x (ez : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → ¬ ez.op.IsDirOp := by
  let D : Nat → Prop := fun x => x < log.length ∧ S x ∧ ∃ e, log[x]? = some e ∧ e.op.IsDirOp
  -- a kept entry after a directory operation keeps it
  have hkeep : ∀ z x (ez : LogEntry), z ≤ x → S x → log[z]? = some ez → ez.op.IsDirOp → D z := by
    intro z x ez hzx hSx hz hd
    have hzL : z < log.length := (List.getElem?_eq_some_iff.1 hz).1
    refine ⟨hzL, ?_, ez, hz, hd⟩
    rcases Nat.lt_or_ge z x with h | h
    · obtain ⟨ex, hx⟩ : ∃ e, log[x]? = some e := ⟨_, List.getElem?_eq_getElem (hS x hSx)⟩
      exact hc x z hSx ⟨h, ex, hx, (hdx z ez hz hd).2 x ex h hx⟩
    · rw [show z = x by omega]; exact hSx
  by_cases hex : ∃ x, x ≤ log.length ∧ D x
  · obtain ⟨x0, hx0, hD0⟩ := hex
    obtain ⟨g, -, hg, hmax⟩ := exists_greatest D log.length ⟨x0, hx0, hD0⟩
    refine ⟨g + 1, hg.1, fun y hy => ?_, fun z x ez h1 h2 hSx hz hd => ?_⟩
    · obtain ⟨-, hSg, eg, heg, hdg⟩ := hg
      rcases Nat.lt_or_ge y g with h | h
      · exact hc g y hSg ⟨h, eg, heg, by rw [(hdx g eg heg hdg).1]; exact h⟩
      · rw [show y = g by omega]; exact hSg
    · have hDz := hkeep z x ez h2 hSx hz hd
      have := hmax z (Nat.le_of_lt hDz.1) hDz
      omega
  · refine ⟨0, Nat.zero_le _, fun y hy => absurd hy (Nat.not_lt_zero _),
      fun z x ez _ h2 hSx hz hd => hex ⟨z, ?_, hkeep z x ez h2 hSx hz hd⟩⟩
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hz).1

/-! ## The replay from `a` on -/

/-- From `a`, a run of file operations keeps the entries naming directories and the keys. -/
theorem run_dirs (hv : LogValid T0 log) {a : Nat} :
    ∀ u, a ≤ u → u ≤ log.length →
      (∀ z (ez : LogEntry), a ≤ z → z < u → log[z]? = some ez → ¬ ez.op.IsDirOp) →
      (∀ j b J, (prefTree T0 log u).entry j b = some (.dir J) ↔
        (prefTree T0 log a).entry j b = some (.dir J)) ∧
      (∀ x, x ∈ prefTree T0 log u ↔ x ∈ prefTree T0 log a)
  | 0, hau, _, _ => by rw [show a = 0 by omega]; exact ⟨fun _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  | u + 1, hau, hu, hf => by
    rcases Nat.lt_or_ge u a with h | h
    · rw [show a = u + 1 by omega]; exact ⟨fun _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩
    obtain ⟨e, he⟩ : ∃ e, log[u]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hnd := hf u e h (Nat.lt_succ_self _) he
    have hok := (hv u e he hnd).1
    obtain ⟨ih1, ih2⟩ := run_dirs hv u h (by omega) (fun z ez h1 h2 hz => hf z ez h1 (by omega) hz)
    rw [prefTree_succ T0 log he]
    exact ⟨fun j b J => (fileOp_dirs hnd hok j b J).trans (ih1 j b J),
      fun x => (fileOp_mem hnd (opOk_slots hnd hok) x).trans (ih2 x)⟩

/-- Below `a`, everything is kept: the replay is the run. -/
theorem kept_prefix {a : Nat} (ha : ∀ y, y < a → S y) :
    ∀ t, t ≤ a → t ≤ log.length → replay (keptUpTo log S t) T0 = prefTree T0 log t
  | 0, _, _ => by simp [keptUpTo, replay, prefTree]
  | t + 1, h1, h2 => by
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [kept_succ T0 log S he, if_pos (ha t (by omega)), prefTree_succ T0 log he,
      kept_prefix ha t (by omega) (by omega)]

/-- The replay's slot, as some tree of the run from `a` on (with file operations only from `a` to
it) has it. -/
theorem kept_slot (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hc : Closed log S) {a : Nat}
    (haL : a ≤ log.length) (ha : ∀ y, y < a → S y)
    (hb : ∀ z x (ez : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → ¬ ez.op.IsDirOp)
    (j : Ino) (b : GoString) :
    ∃ g, a ≤ g ∧ g ≤ log.length ∧
      (∀ z (ez : LogEntry), a ≤ z → z < g → log[z]? = some ez → ¬ ez.op.IsDirOp) ∧
      (replay (keptUpTo log S log.length) T0).entry j b = (prefTree T0 log g).entry j b := by
  rw [kept_entry hps hdx hc log.length (Nat.le_refl _)]
  unfold slotV
  have hsp := lastW_spec log S j b log.length
  -- no writer below `a` after the last kept one
  have hfr : ∀ u, u ≤ a → (∀ y, u ≤ y → y < log.length → ¬ KW log S y j b) →
      (prefTree T0 log a).entry j b = (prefTree T0 log u).entry j b := fun u hu hk =>
    prefTree_frame T0 log a hu haL (fun y e h1 h2 he hw =>
      hk y h1 (by omega) ⟨ha y h2, e, he, hw⟩)
  revert hsp
  cases lastW log S log.length j b with
  | some w =>
    rintro ⟨hw1, hw2, hw3⟩
    rcases Nat.lt_or_ge w a with h | h
    · refine ⟨a, Nat.le_refl _, haL, fun z ez h1 h2 => absurd h2 (by omega), ?_⟩
      exact (hfr (w + 1) (by omega) (fun y h1 h2 => hw3 y (by omega) h2)).symm
    · exact ⟨w + 1, by omega, by omega, fun z ez h1 h2 hz => hb z w ez h1 (by omega) hw2.1 hz, rfl⟩
  | none =>
    intro hk
    refine ⟨a, Nat.le_refl _, haL, fun z ez h1 h2 => absurd h2 (by omega), ?_⟩
    rw [hfr 0 (Nat.zero_le _) (fun y _ h2 => hk y h2), prefTree_zero]

/-- Some tree of the run, not later than `t`, has the replay's slot. -/
theorem kept_slot_le (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hc : Closed log S) {t : Nat}
    (ht : t ≤ log.length) (j : Ino) (b : GoString) :
    ∃ g, g ≤ t ∧ (replay (keptUpTo log S t) T0).entry j b = (prefTree T0 log g).entry j b := by
  rw [kept_entry hps hdx hc t ht]
  unfold slotV
  have hsp := lastW_spec log S j b t
  revert hsp
  cases lastW log S t j b with
  | some w => rintro ⟨hw1, -, -⟩; exact ⟨w + 1, by omega, rfl⟩
  | none => intro _; exact ⟨0, Nat.zero_le _, by rw [prefTree_zero]⟩

/-- From `a` on, the replay has the directory keys of `T a`. -/
theorem kept_keys (hv : LogValid T0 log) {a : Nat} (ha : ∀ y, y < a → S y)
    (hb : ∀ z x (ez : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → ¬ ez.op.IsDirOp) :
    ∀ t, a ≤ t → t ≤ log.length → ∀ x,
      x ∈ replay (keptUpTo log S t) T0 ↔ x ∈ prefTree T0 log a
  | 0, hat, hL => by
    rw [show a = 0 by omega, kept_prefix ha 0 (by omega) hL]; exact fun _ => Iff.rfl
  | t + 1, hat, hL => by
    rcases Nat.lt_or_ge t a with h | h
    · rw [show a = t + 1 by omega, kept_prefix ha (t + 1) (by omega) hL]; exact fun _ => Iff.rfl
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ih := kept_keys hv ha hb t h (by omega)
    rw [kept_succ T0 log S he]
    by_cases hS : S t
    · rw [if_pos hS]
      have hnd := hb t t e h (Nat.le_refl _) hS he
      have hok := (hv t e he hnd).1
      have hrd := (run_dirs hv t h (by omega)
        (fun z ez h1 h2 hz => hb z t ez h1 (by omega) hS hz)).2
      intro x
      rw [fileOp_mem hnd (fun sl hsl => (ih _).2 ((hrd _).1 (opOk_slots hnd hok sl hsl))) x]
      exact ih x
    · rw [if_neg hS]; exact ih

/-- From `a` on, the replay names each file once. -/
theorem kept_inj (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hv : LogValid T0 log)
    {R : List (GoString × Ino)} (hwf : ∀ t, t ≤ log.length → TreeWf R (prefTree T0 log t))
    (hc : Closed log S) {a : Nat} (ha : ∀ y, y < a → S y)
    (hb : ∀ z x (ez : LogEntry), a ≤ z → z ≤ x → S x → log[z]? = some ez → ¬ ez.op.IsDirOp) :
    ∀ t, a ≤ t → t ≤ log.length → ∀ j1 b1 j2 b2 i,
      (replay (keptUpTo log S t) T0).entry j1 b1 = some (.file i) →
      (replay (keptUpTo log S t) T0).entry j2 b2 = some (.file i) → j1 = j2 ∧ b1 = b2
  | 0, hat, hL => by
    rw [kept_prefix ha 0 (by omega) hL]
    exact fun j1 b1 j2 b2 _ h1 h2 => (hwf 0 hL).2.2.2.2 j1 b1 j2 b2 _ h1 h2
  | t + 1, hat, hL => by
    rcases Nat.lt_or_ge t a with h | h
    · rw [kept_prefix ha (t + 1) (by omega) hL]
      exact fun j1 b1 j2 b2 _ h1 h2 => (hwf (t + 1) hL).2.2.2.2 j1 b1 j2 b2 _ h1 h2
    obtain ⟨e, he⟩ : ∃ e, log[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ih := kept_inj hps hdx hv hwf hc ha hb t h (by omega)
    rw [kept_succ T0 log S he]
    by_cases hS : S t
    · rw [if_pos hS]
      have hnd := hb t t e h (Nat.le_refl _) hS he
      have hval := hv t e he hnd
      have hA := kept_entry hps hdx hc (T0 := T0) t (by omega)
      have hrd := kept_reads hps hdx hc he hS hA
      have hfresh : ∀ j0 b0 i0, e.op = .create j0 b0 i0 → ∀ j b,
          (replay (keptUpTo log S t) T0).entry j b ≠ some (.file i0) := by
        intro j0 b0 i0 hop j b hjb
        obtain ⟨g, hg, hgeq⟩ := kept_slot_le (T0 := T0) hps hdx hc (t := t) (by omega) j b
        exact hval.2 j0 b0 i0 hop g hg ⟨j, b, hgeq ▸ hjb⟩
      revert hnd hval hrd hfresh
      generalize replay (keptUpTo log S t) T0 = K at ih ⊢
      intro hnd hval hrd hfresh
      cases hop : e.op with
      | create j0 b0 i0 =>
        rw [hop] at hval
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
      | rename j0 b0 j1' b1' n old =>
        rw [hop] at hval
        have hr : K.entry j0 b0 = some n :=
          (hrd (j0, b0) (by rw [hop]; simp [MetaOp.slots])).trans hval.1.2.2.1
        intro j1 b1 j2 b2 i h1 h2
        rw [entry_rename, hr] at h1 h2
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
      | mkdir => exact absurd (by rw [hop]; trivial) hnd
    · rw [if_neg hS]; exact ih

/-- **The consistent-cut theorem** (`TreeCut.lean` states the disciplines). -/
theorem closed_cut {R : List (GoString × Ino)}
    (_hst : Starts log) (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hv : LogValid T0 log)
    (hwf : ∀ t, t ≤ log.length → TreeWf R (prefTree T0 log t))
    (hS : ∀ x, S x → x < log.length) (hc : Closed log S) :
    TreeWf R (replay (keptOps log S) T0) ∧
    (∀ j b, (replay (keptOps log S) T0).entry j b = slotAfter T0 log S j b) ∧
    (∀ i, Named (replay (keptOps log S) T0) i → ∃ t, t ≤ log.length ∧ Named (prefTree T0 log t) i) ∧
    (∃ t, t ≤ log.length ∧ ∀ j, j ∈ replay (keptOps log S) T0 ↔ j ∈ prefTree T0 log t) := by
  obtain ⟨a, haL, ha, hb⟩ := cut_base hdx hc hS
  have hK : keptOps log S = keptUpTo log S log.length := rfl
  rw [hK]
  have hkeys := kept_keys hv ha hb log.length haL (Nat.le_refl _)
  have hinj := kept_inj hps hdx hv hwf hc ha hb log.length haL (Nat.le_refl _)
  have hdirs : ∀ j b J, (replay (keptUpTo log S log.length) T0).entry j b = some (.dir J) ↔
      (prefTree T0 log a).entry j b = some (.dir J) := by
    intro j b J
    obtain ⟨g, hg1, hg2, hgw, heq⟩ := kept_slot (T0 := T0) hps hdx hc haL ha hb j b
    rw [heq]; exact (run_dirs hv g hg1 hg2 hgw).1 j b J
  refine ⟨?_, fun j b => kept_entry hps hdx hc log.length (Nat.le_refl _) j b, ?_, ⟨a, haL, hkeys⟩⟩
  · refine treeWf_sameDirs (hwf a haL) hkeys hdirs ?_ ?_ ?_
    · intro x hx _ b
      obtain ⟨g, hg1, hg2, hgw, heq⟩ := kept_slot (T0 := T0) hps hdx hc haL ha hb x b
      rw [heq]
      obtain ⟨hd, -⟩ := run_dirs hv g hg1 hg2 hgw
      by_cases hxg : x ∈ prefTree T0 log g
      · rcases (hwf g hg2).2.1 x hxg with hr | ⟨he, -⟩
        · exact absurd (reach_mono (fun j b j' h => (hd j b j').1 h) hr) hx
        · exact he b
      · have h0 : (prefTree T0 log g) !! x = none := by
          cases h : (prefTree T0 log g) !! x with
          | none => rfl
          | some _ => exact absurd (by rw [GMap.mem_iff, h]; rfl) hxg
        simp [Tree.entry, h0]
    · intro j b n he
      obtain ⟨g, -, hg2, -, heq⟩ := kept_slot (T0 := T0) hps hdx hc haL ha hb j b
      rw [heq] at he; exact ((hwf g hg2).2.2.1 j b n he).1
    · intro j1 b1 j2 b2 n h1 h2
      cases n with
      | file i => exact hinj j1 b1 j2 b2 i h1 h2
      | dir J => exact (hwf a haL).2.2.2.2 j1 b1 j2 b2 _ ((hdirs _ _ _).1 h1) ((hdirs _ _ _).1 h2)
  · rintro i ⟨j, b, h⟩
    obtain ⟨g, -, hg2, -, heq⟩ := kept_slot (T0 := T0) hps hdx hc haL ha hb j b
    exact ⟨g, hg2, j, b, heq ▸ h⟩

end cut

end Fs
end Perennial

end
