/-
The shared mode of the tree: a step that logs an entry (`wp_logStepS`), the generic lemma of the
logging steps (`Unlink`, the file `Rename`s, `Mkdir`, `Rmdir`, the directory `Rename`), as
`wp_callEndS` is for the steps that only end their call (`notes/wal-fsext-i2-design.md`,
"Implementation log", note 13). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Pure facts: a log with one more entry -/

theorem lt_lastSat (P : Nat → Bool) : ∀ n y, y < n → P y = true → y < lastSat n P := by
  intro n
  induction n with
  | zero => intro y hy; omega
  | succ n ih =>
    intro y hy hP
    rw [lastSat_succ]
    by_cases hn : P n = true
    · simp only [hn, if_true]; omega
    · simp only [hn]
      have hyn : y ≠ n := fun h => by subst h; exact hn hP
      exact ih y (by omega) hP

open Classical in
/-- An entry writing a name of a claim is below its `next`. -/
theorem lt_namesOf_next {V : Hist} {j : Ino} {N : NameSet} {y : Nat} {ey : LogEntry}
    {b : GoString} (hy : V.2[y]? = some ey) (hb : N.Mem b) (hw : ey.op.Writes j b) :
    y < (namesOf V j N).next := by
  rw [namesOf_next]
  exact lt_lastSat _ _ _ (List.getElem?_eq_some_iff.1 hy).1 (decide_eq_true ⟨ey, hy, b, hb, hw⟩)

theorem restrictN_lookup_not (N : NameSet) (e : Ents) (b : GoString) (hb : ¬ N.Mem b) :
    restrictN N e !! b = none := by
  unfold restrictN
  rw [GMap.lookup_filter]
  cases e !! b <;> simp [hb]

theorem restrictN_apply_other (o : MetaOp) (m : Tree) (j : Ino) (N : NameSet)
    (h : ∀ b, N.Mem b → ¬ o.Writes j b) :
    restrictN N (entsOf (o.apply m) j) = restrictN N (entsOf m j) := by
  apply GMap.ext; intro b
  by_cases hb : N.Mem b
  · show restrictN N (entsOf (o.apply m) j) !! b = restrictN N (entsOf m j) !! b
    rw [restrictN_lookup _ _ _ hb, restrictN_lookup _ _ _ hb, entsOf_lookup, entsOf_lookup,
      apply_other _ _ _ _ (h b hb)]
  · show restrictN N (entsOf (o.apply m) j) !! b = restrictN N (entsOf m j) !! b
    rw [restrictN_lookup_not _ _ _ hb, restrictN_lookup_not _ _ _ hb]

theorem prefTree_snoc_le (T0 : Tree) (log : List LogEntry) (e : LogEntry) {t : Nat}
    (ht : t ≤ log.length) : prefTree T0 (log ++ [e]) t = prefTree T0 log t := by
  simp [prefTree, List.take_append_of_le_length ht]

theorem hist_now_snoc (V : Hist) (e : LogEntry) :
    Hist.now (V.1, V.2 ++ [e]) = e.op.apply V.now := by
  simp [Hist.now, Hist.ops, replay_snoc]

theorem prefTree_snoc_len (V : Hist) (e : LogEntry) :
    prefTree V.1 (V.2 ++ [e]) (V.2.length + 1) = e.op.apply V.now := by
  rw [← hist_now_snoc]
  simp only [prefTree, Hist.now, Hist.ops]
  rw [List.take_of_length_le (by simp)]

theorem NamesH.ext' {h h' : NamesH} (h1 : h.boot = h'.boot) (h2 : h.ents = h'.ents)
    (h3 : h.cur = h'.cur) : h = h' := by
  cases h; cases h'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

open Classical in
/-- The ents of a claim, with one more entry in the log. -/
theorem namesOf_ents_snoc (V : Hist) (e : LogEntry) (j : Ino) (N : NameSet) :
    (namesOf (V.1, V.2 ++ [e]) j N).ents = (namesOf V j N).ents ++
      (if ∃ b, N.Mem b ∧ e.op.Writes j b then
        [(V.2.length, e, restrictN N (entsOf (e.op.apply V.now) j))] else []) := by
  rw [namesOf_ents, namesOf_ents]
  simp only [List.length_append, List.length_singleton]
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  · rw [List.filter_congr (q := fun x => decide
        (∃ e', V.2[x]? = some e' ∧ ∃ b, N.Mem b ∧ e'.op.Writes j b))]
    · apply List.map_congr_left
      intro x hx
      have hxl : x < V.2.length := List.mem_range.1 (List.mem_filter.1 hx).1
      rw [List.getElem?_append_left hxl, prefTree_snoc_le _ _ _ (by omega)]
    · intro x hx
      have hxl : x < V.2.length := List.mem_range.1 hx
      rw [List.getElem?_append_left hxl]
  · have hl : (V.2 ++ [e])[V.2.length]? = some e := by simp
    by_cases hw : ∃ b, N.Mem b ∧ e.op.Writes j b
    · rw [if_pos hw]
      simp only [List.filter_cons, List.filter_nil, hl]
      rw [if_pos (by simpa using hw)]
      simp only [List.map_cons, List.map_nil, hl, Option.getD_some, prefTree_snoc_len]
    · rw [if_neg hw]
      simp only [List.filter_cons, List.filter_nil, hl]
      rw [if_neg (by simpa using hw)]
      rfl

/-- A claim none of whose names an entry writes: the same with the entry logged. -/
theorem namesOf_snoc_other (V : Hist) (e : LogEntry) (j : Ino) (N : NameSet)
    (h : ∀ b, N.Mem b → ¬ e.op.Writes j b) : namesOf (V.1, V.2 ++ [e]) j N = namesOf V j N := by
  refine NamesH.ext' rfl ?_ ?_
  · rw [namesOf_ents_snoc, if_neg (fun ⟨b, hb, hw⟩ => h b hb hw), List.append_nil]
  · show restrictN N (entsOf (Hist.now (V.1, V.2 ++ [e])) j) = restrictN N (entsOf V.now j)
    rw [hist_now_snoc, restrictN_apply_other _ _ _ _ h]

/-- A claim one of whose names an entry writes: the entry recorded. -/
theorem namesOf_snoc_written (V : Hist) (e : LogEntry) (j : Ino) (N : NameSet)
    (h : ∃ b, N.Mem b ∧ e.op.Writes j b) :
    namesOf (V.1, V.2 ++ [e]) j N =
      (namesOf V j N).log V.2.length e (restrictN N (entsOf (e.op.apply V.now) j)) := by
  refine NamesH.ext' rfl ?_ ?_
  · rw [namesOf_ents_snoc, if_pos h]; rfl
  · show restrictN N (entsOf (Hist.now (V.1, V.2 ++ [e])) j) = _
    rw [hist_now_snoc]; rfl

/-- The log as a map, with one more entry. -/
theorem logMap_snoc (log : List LogEntry) (e : LogEntry) :
    logMap (log ++ [e]) = <[log.length := e]> (logMap log) := by
  apply GMap.ext; intro x
  show logMap (log ++ [e]) !! x = (<[log.length := e]> (logMap log)) !! x
  rw [logMap_lookup]
  by_cases hx : log.length = x
  · subst hx; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ hx, logMap_lookup]
    by_cases hlt : x < log.length
    · rw [List.getElem?_append_left hlt]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- An operation touches only names it writes. -/
theorem touched_writes (o : MetaOp) (j : Ino) (b : GoString) (h : b ∈ o.touched j) :
    o.Writes j b := by
  left
  cases o with
  | create j0 b0 i =>
    simp only [MetaOp.touched] at h; split at h
    · simp at h; subst h; rename_i hj; subst hj; simp [MetaOp.slots]
    · simp at h
  | mkdir j0 b0 J =>
    simp only [MetaOp.touched] at h; split at h
    · simp at h; subst h; rename_i hj; subst hj; simp [MetaOp.slots]
    · simp at h
  | remove j0 b0 n =>
    simp only [MetaOp.touched] at h; split at h
    · simp at h; subst h; rename_i hj; subst hj; simp [MetaOp.slots]
    · simp at h
  | rename j0 b0 j1 b1 n old =>
    simp only [MetaOp.touched, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h; subst h; rename_i hj; subst hj; simp [MetaOp.slots]
      · simp at h
    · split at h
      · simp at h; subst h; rename_i hj; subst hj; simp [MetaOp.slots]
      · simp at h

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

/-- The directories an operation makes. -/
def MetaOp.newDirs : MetaOp → List Ino
  | .mkdir _ _ J => [J]
  | _ => []

theorem newDirs_cases (o : MetaOp) :
    o.newDirs = [] ∨ ∃ j b J, o = .mkdir j b J ∧ o.newDirs = [J] := by
  cases o with
  | mkdir j b J => exact .inr ⟨j, b, J, rfl, rfl⟩
  | _ => exact .inl rfl

theorem mem_apply_newDirs (o : MetaOp) (m : Tree) (J : Ino) (h : J ∈ o.newDirs) :
    J ∈ o.apply m := by
  cases o with
  | mkdir j b J' =>
    simp only [MetaOp.newDirs, List.mem_singleton] at h; subst h
    simp only [MetaOp.apply]; rw [GMap.mem_iff, GMap.lookup_insert]; rfl
  | _ => simp [MetaOp.newDirs] at h

/-- What an operation writes: its slots, or a name of a directory it makes. -/
theorem writes_cases (o : MetaOp) (j : Ino) (b : GoString) (h : o.Writes j b) :
    (j, b) ∈ o.slots ∨ j ∈ o.newDirs := by
  rcases h with h | ⟨j0, b0, rfl⟩
  · exact .inl h
  · exact .inr (by simp [MetaOp.newDirs])

theorem adds_touched (o : MetaOp) (j : Ino) (b : GoString) (h : b ∈ o.adds j) : b ∈ o.touched j := by
  cases o <;> simp only [MetaOp.adds, MetaOp.touched, List.mem_append] at h ⊢
  all_goals first | exact h | exact Or.inr h | simp at h

theorem note_ino (o : MetaOp) (df : OsDirFd) : (df.note o).ino = df.ino := by
  unfold OsDirFd.note; split <;> rfl

theorem getElem?_snoc_cases {α : Type} {l : List α} {a b : α} {x : Nat} (h : (l ++ [a])[x]? = some b) :
    (x < l.length ∧ l[x]? = some b) ∨ (x = l.length ∧ b = a) := by
  by_cases hx : x < l.length
  · rw [List.getElem?_append_left hx] at h; exact .inl ⟨hx, h⟩
  · have hx' : x < l.length + 1 := by
      have := (List.getElem?_eq_some_iff.1 h).1; simpa using this
    have hxe : x = l.length := by omega
    subst hxe; simp at h; exact .inr ⟨rfl, h.symm⟩

theorem tree_prefTree (st : OsState) :
    st.tree = prefTree st.fs.treeDur st.fs.metaLog st.fs.metaLog.length := by
  simp [prefTree, OsState.tree]

/-- A shared read's coherence, after an entry is logged and the read told of it. -/
theorem phOkS_note {st st' : OsState} {j : Ino} {x : DirPhS} {df : OsDirFd} {o : MetaOp} {s0 : Nat}
    (hj : df.ino = j) (h : PhOkS st j x df.rd)
    (hlog : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s0⟩]) (htree : st'.tree = o.apply st.tree)
    (hadd : ∀ j b, b ∈ o.adds j → NameOk b) : PhOkS st' j x (df.note o).rd := by
  cases x with
  | idle => cases hr : df.rd <;> simp [PhOkS, OsDirFd.note, hr] at h ⊢
  | done => cases hr : df.rd <;> simp [PhOkS, OsDirFd.note, hr] at h ⊢
  | reading N r0 rs =>
    cases hr : df.rd with
    | idle => simp [PhOkS, hr] at h
    | done => simp [PhOkS, hr] at h
    | reading u s r =>
      simp only [PhOkS, hr] at h
      simp only [OsDirFd.note, hr, PhOkS]
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨by rw [hlog]; simp; omega, fun b hb => ?_, fun hn b hb => ?_⟩
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
        rcases hb with hb | hb
        · exact h2 b hb
        · exact hadd _ b hb
      · have hnw : ∀ b, N.Mem b → ¬ o.Writes j b := fun b hb hw =>
          hn st.fs.metaLog.length ⟨o, s0⟩ h1 (by rw [hlog]; simp) b hb hw
        have hold := h3 (fun x e hx he => hn x e hx (by
          have hxl := (List.getElem?_eq_some_iff.1 he).1
          rw [hlog, List.getElem?_append_left hxl]; exact he)) b hb
        have hp : present st' j b = present st j b := by
          simp only [present, htree, apply_other _ _ _ _ (hnw b hb)]
        have hnt : b ∉ o.touched df.ino := fun ht => hnw b hb (hj ▸ touched_writes o df.ino b ht)
        have hna : b ∉ o.adds df.ino := fun ha => hnt (adds_touched _ _ _ ha)
        obtain ⟨hu, hs, hr'⟩ := hold
        refine ⟨?_, ?_, ?_⟩
        · rw [hp, ← hu]; simp [hnt]
        · rw [hp, ← hs]; simp [hna]
        · rw [← hr']; simp [hnt]

/-- **The shared coherence after a step that logged `o`** for the call `k` (begun at `s0`, holding
`q` of the permission). -/
theorem treeCohS_log {st st' : OsState} {s1 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc : GMap Nat (Nat × Qp)} (hc : TreeCohS st s1 Γdf Γc) {k s0 : Nat} {q : Qp}
    (hk : Γc !! k = some (s0, q)) (o : MetaOp)
    (hdur : st'.fs.treeDur = st.fs.treeDur)
    (hlog : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s0⟩])
    (hdf : st'.proc.dfds = GMap.fmap (·.note o) st.proc.dfds)
    (hca : st'.proc.calls = GMap.delete k st.proc.calls)
    (htree : st'.tree = o.apply st.tree)
    (hpss : ∀ y (ey : LogEntry), st.fs.metaLog[y]? = some ey →
      (∃ sl ∈ o.slots, sl ∈ ey.op.slots) → y < s0)
    (hdir : o.IsDirOp → q = 1)
    (hexcl : ∀ t x, t ≠ k → Γc !! t = some x → x.2.val < 1 ∧ q.val < 1)
    (hok : ¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
      t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i)
    (hadd : ∀ j b, b ∈ o.adds j → NameOk b) :
    TreeCohS st' s1 Γdf (GMap.delete k Γc) := by
  have hle : s0 ≤ st.fs.metaLog.length := hc.callsLe k _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x e hx
    rw [hlog] at hx
    rcases getElem?_snoc_cases hx with ⟨-, hx⟩ | ⟨rfl, rfl⟩
    · exact hc.starts x e hx
    · exact hle
  · intro x y ex ey hyx hx hy hsl
    rw [hlog] at hx hy
    rcases getElem?_snoc_cases hx with ⟨hxl, hx⟩ | ⟨rfl, rfl⟩
    · rcases getElem?_snoc_cases hy with ⟨-, hy⟩ | ⟨rfl, -⟩
      · exact hc.pss x y ex ey hyx hx hy hsl
      · omega
    · rcases getElem?_snoc_cases hy with ⟨-, hy⟩ | ⟨rfl, -⟩
      · exact hpss y ey hy hsl
      · omega
  · intro x ex hx hd
    rw [hlog] at hx
    rcases getElem?_snoc_cases hx with ⟨hxl, hx⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := hc.dox x ex hx hd
      refine ⟨h1, fun z ez hxz hz => ?_⟩
      rw [hlog] at hz
      rcases getElem?_snoc_cases hz with ⟨-, hz⟩ | ⟨rfl, rfl⟩
      · exact h2 z ez hxz hz
      · exact hc.after k _ hk x ex hx hd
    · have hdo : o.IsDirOp := by
        rcases hd with hd | hd
        · exact hd
        · have := hc.s0le; omega
      have hs : s0 = st.fs.metaLog.length := hc.whole k _ hk (hdir hdo)
      refine ⟨hs, fun z ez hxz hz => ?_⟩
      rw [hlog] at hz
      have := (List.getElem?_eq_some_iff.1 hz).1
      simp at this; omega
  · intro x e hx hnd
    rw [hdur]
    rw [hlog] at hx
    rcases getElem?_snoc_cases hx with ⟨hxl, hx⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := hc.valid x e hx hnd
      rw [hlog, prefTree_snoc_le _ _ _ (Nat.le_of_lt hxl)]
      refine ⟨h1, fun j b i he t ht => ?_⟩
      rw [prefTree_snoc_le _ _ _ (by omega)]
      exact h2 j b i he t ht
    · have hnd' : ¬ o.IsDirOp := fun h => hnd (.inl h)
      obtain ⟨h1, h2⟩ := hok hnd'
      rw [hlog, prefTree_snoc_le _ _ _ (Nat.le_refl _), ← tree_prefTree]
      refine ⟨h1, fun j b i he t ht => ?_⟩
      rw [prefTree_snoc_le _ _ _ ht]
      exact h2 j b i he t ht
  · rw [hlog]; simp; have := hc.s0le; omega
  · intro fd
    rw [hdf, GMap.lookup_fmap, hc.fds fd]
    cases st.proc.dfds !! fd <;> simp [note_ino]
  · intro fd x df' hx hdf'
    rw [hdf, GMap.lookup_fmap] at hdf'
    cases hd : st.proc.dfds !! fd with
    | none => rw [hd] at hdf'; simp at hdf'
    | some df =>
      rw [hd] at hdf'; simp only [Option.map_some, Option.some.injEq] at hdf'
      subst hdf'
      have hino : x.1 = df.ino := by
        have := hc.fds fd; rw [hx, hd] at this; simpa using this
      exact phOkS_note hino.symm (hc.ph fd x df hx hd) hlog htree hadd
  · intro t
    rw [hca]
    by_cases h0 : k = t
    · subst h0; simp
    · rw [GMap.lookup_delete_ne _ h0, GMap.lookup_delete_ne _ h0]; exact hc.calls t
  · intro t x hx
    by_cases h0 : k = t
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx
      rw [hlog]; simp; have := hc.callsLe t x hx; omega
  · intro t x hx hq
    by_cases h0 : k = t
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx
      have := (hexcl t x (Ne.symm h0) hx).1
      rw [hq] at this; exact absurd this (by simp)
  · intro t x hx y ey hy hd
    by_cases h0 : k = t
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx
      rw [hlog] at hy
      rcases getElem?_snoc_cases hy with ⟨-, hy⟩ | ⟨rfl, rfl⟩
      · exact hc.after t x hx y ey hy hd
      · rcases hd with hd | hd
        · have := (hexcl t x (Ne.symm h0) hx).2
          rw [hdir hd] at this; exact absurd this (by simp)
        · have := hc.s0le; omega

end Fs
end Perennial

end
