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

/-! ## The claims after a logged entry -/

/-- The claims `ks` set to their histories in `V'`. -/
def insKeys (V' : Hist) (ks : List (Ino × NameSet)) (m : GMap (Ino × NameSet) NamesH) :
    GMap (Ino × NameSet) NamesH :=
  ks.foldr (fun k m => <[k := namesOf V' k.1 k.2]> m) m

theorem insKeys_lookup (V' : Hist) (ks : List (Ino × NameSet)) (m : GMap (Ino × NameSet) NamesH)
    (k : Ino × NameSet) :
    insKeys V' ks m !! k = if k ∈ ks then some (namesOf V' k.1 k.2) else m !! k := by
  induction ks with
  | nil => simp [insKeys]
  | cons k0 ks ih =>
    show (<[k0 := namesOf V' k0.1 k0.2]> (insKeys V' ks m)) !! k = _
    by_cases h : k0 = k
    · subst h; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ h, ih]
      have : k ∈ k0 :: ks ↔ k ∈ ks := by simp [Ne.symm h]
      simp only [this]

/-- The keys of the claims a step makes: one on all the names of each directory it makes. -/
def newKeys (o : MetaOp) : List (Ino × NameSet) := o.newDirs.map (fun J => (J, .except []))

/-- **The claims' coherence after a logged entry**: the presented claims `ks` (each existing) and
the new directories' claims set to the new history's; every slot the entry writes is in a presented
claim; a new directory is new. -/
theorem namesCoh_log {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} (hcoh : NamesCoh V Γn)
    (e : LogEntry) (ks : List (Ino × NameSet))
    (hin : ∀ k ∈ ks, ∃ h, Γn !! k = some h)
    (hslots : ∀ sl ∈ e.op.slots, ∃ k ∈ ks, k.1 = sl.1 ∧ k.2.Mem sl.2)
    (hnew : ∀ J ∈ e.op.newDirs, J ∉ V.now)
    (hdirs : ∀ x, x ∈ e.op.apply V.now → x ∈ V.now ∨ x ∈ e.op.newDirs) :
    NamesCoh (V.1, V.2 ++ [e]) (insKeys (V.1, V.2 ++ [e]) (newKeys e.op ++ ks) Γn) := by
  have hnowV : Hist.now (V.1, V.2 ++ [e]) = e.op.apply V.now := hist_now_snoc V e
  have hnk : ∀ k ∈ newKeys e.op, k.2 = .except [] ∧ k.1 ∈ e.op.newDirs := by
    intro k hk
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hk
    exact ⟨rfl, hJ⟩
  have horig : ∀ k h, insKeys (V.1, V.2 ++ [e]) (newKeys e.op ++ ks) Γn !! k = some h →
      (∃ h0, Γn !! k = some h0) ∨ k ∈ newKeys e.op := by
    intro k h hl
    rw [insKeys_lookup] at hl
    split at hl
    · rename_i hk
      rcases List.mem_append.1 hk with hk | hk
      · exact .inr hk
      · exact .inl (hin k hk)
    · exact .inl ⟨h, hl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j N h hl
    rw [insKeys_lookup] at hl
    split at hl
    · cases hl; rfl
    · rename_i hk
      rw [hcoh.hist j N h hl]
      symm
      apply namesOf_snoc_other
      intro b hb hw
      rcases writes_cases _ _ _ hw with hs | hd
      · obtain ⟨k', hk', hk1, hk2⟩ := hslots (j, b) hs
        obtain ⟨h', hl'⟩ := hin k' hk'
        have hk'e : k' = (j, k'.2) := by simp only at hk1; rw [← hk1]
        by_cases hN : k'.2 = N
        · exact hk (List.mem_append.2 (.inr (by rw [hk'e, hN] at hk'; exact hk')))
        · rw [hk'e] at hl'
          exact hcoh.disj j k'.2 N h' h b hl' hl hN hk2 hb
      · exact hnew j hd (hcoh.dirs j N h hl)
  · intro j N N' h h' b hl hl' hne hb hb'
    rcases horig _ _ hl with ⟨h0, hl0⟩ | hk
    · rcases horig _ _ hl' with ⟨h0', hl0'⟩ | hk'
      · exact hcoh.disj j N N' h0 h0' b hl0 hl0' hne hb hb'
      · exact hnew j (hnk _ hk').2 (hcoh.dirs j N h0 hl0)
    · rcases horig _ _ hl' with ⟨h0', hl0'⟩ | hk'
      · exact hnew j (hnk _ hk).2 (hcoh.dirs j N' h0' hl0')
      · exact hne ((hnk _ hk).1.trans (hnk _ hk').1.symm)
  · intro j b hj
    rw [hnowV] at hj
    rcases hdirs j hj with hj | hj
    · obtain ⟨N, h, hl, hm⟩ := hcoh.cover j b hj
      by_cases hk : (j, N) ∈ newKeys e.op ++ ks
      · exact ⟨N, _, by rw [insKeys_lookup, if_pos hk], hm⟩
      · exact ⟨N, h, by rw [insKeys_lookup, if_neg hk]; exact hl, hm⟩
    · refine ⟨.except [], namesOf (V.1, V.2 ++ [e]) j (.except []), ?_, by simp [NameSet.Mem]⟩
      rw [insKeys_lookup, if_pos (List.mem_append.2 (.inl (show (j, NameSet.except []) ∈ newKeys e.op from List.mem_map.2 ⟨j, hj, rfl⟩)))]
  · intro j N h hl
    show j ∈ Hist.now (V.1, V.2 ++ [e])
    rw [hnowV]
    rcases horig _ _ hl with ⟨h0, hl0⟩ | hk
    · exact mem_apply_of_mem _ _ _ (hcoh.dirs j N h0 hl0)
    · exact mem_apply_newDirs _ _ _ (hnk _ hk).2

/-! ## The step -/

/-- A claim a logging step writes: its directory, its names, what it knows, and its names' entries
after the step. -/
abbrev ClaimW := Ino × NameSet × NamesH × Ents

/-- What the claims know of the tree of `st`: their names' entries; no other name in what they
know; two claims of one directory under distinct keys share no name. -/
structure ClaimsAt (st : OsState) (cl : List ClaimW) : Prop where
  ent : ∀ c ∈ cl, ∀ b, c.2.1.Mem b → st.tree.entry c.1 b = c.2.2.1.cur !! b
  out : ∀ c ∈ cl, ∀ b, ¬ c.2.1.Mem b → c.2.2.1.cur !! b = none
  disj : ∀ c ∈ cl, ∀ c' ∈ cl, c.1 = c'.1 → c.2.1 ≠ c'.2.1 → ∀ b, c.2.1.Mem b → ¬ c'.2.1.Mem b

/-- `st'` is `st` after a step of the call `k` (begun at `s0`) that logged `o`, the next inode
perhaps taken, the files as they were. -/
structure LoggedFrom (st st' : OsState) (k s0 : Nat) (o : MetaOp) : Prop where
  roots : st'.fs.roots = st.fs.roots
  dur : st'.fs.treeDur = st.fs.treeDur
  log : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s0⟩]
  committed : st'.fs.committed = st.fs.committed
  dfds : st'.proc.dfds = GMap.fmap (·.note o) st.proc.dfds
  calls : st'.proc.calls = GMap.delete k st.proc.calls
  next : st.fs.nextIno ≤ st'.fs.nextIno
  same : FilesSame st st'

theorem loggedFrom_metaDo (st : OsState) (k s0 : Nat) (o : MetaOp) :
    LoggedFrom st ((st.metaEnd k).metaDo o s0) k s0 o :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem loggedFrom_metaDoIno (st : OsState) (k s0 : Nat) (o : MetaOp) :
    LoggedFrom st ((st.metaEnd k).takeIno.metaDo o s0) k s0 o :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_succ _, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem LoggedFrom.tree {st st' : OsState} {k s0 : Nat} {o : MetaOp} (h : LoggedFrom st st' k s0 o) :
    st'.tree = o.apply st.tree := by
  simp only [OsState.tree, h.dur, h.log, List.map_append, List.map_cons, List.map_nil]
  rw [replay_snoc]

theorem LoggedFrom.wf {st st' : OsState} {k s0 : Nat} {o : MetaOp} (h : LoggedFrom st st' k s0 o)
    (hw : FsTreeWf st) (htw : TreeWf st.fs.roots (o.apply st.tree))
    (hnm : ∀ i, Named (o.apply st.tree) i → Named st.tree i)
    (hlt : ∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) : FsTreeWf st' := by
  obtain ⟨-, hnamed, -⟩ := wf_tree hw
  refine fsTreeWf_meta hw h.roots h.dur h.log (fun i f hf => ⟨f, by rw [h.same.1]; exact hf⟩)
    h.next htw (fun i hi => by
      obtain ⟨f, hf⟩ := hnamed i (hnm i hi)
      exact ⟨f, by rw [h.same.1]; exact hf⟩) hlt (fun fd df hdf => ?_) (fun fd hfd => ?_)
    (fun i hi => ?_)
  · rw [h.dfds, GMap.lookup_fmap] at hdf
    cases hd : st.proc.dfds !! fd with
    | none => rw [hd] at hdf; simp at hdf
    | some df0 =>
      rw [hd] at hdf; simp only [Option.map_some, Option.some.injEq] at hdf
      subst hdf; rw [note_ino]; exact hw.dfds fd df0 hd
  · rw [h.dfds, GMap.lookup_fmap, hw.disj fd (by rw [← h.same.2.1]; exact hfd)]; rfl
  · rw [h.same.1] at hi; exact Nat.lt_of_lt_of_le (hw.files_lt i hi) h.next

theorem histMap_insert (RV RV' : Roots × Hist) : <[() := RV']> (histMap RV) = histMap RV' := by
  apply GMap.ext; intro u
  cases u
  show (<[() := RV']> (histMap RV)) !! () = histMap RV' !! ()
  rw [GMap.lookup_insert]; simp [histMap]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem logEnt_persist (x : Nat) (e : LogEntry) :
    ⊢ gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog x (DFrac.own 1) e ==∗
      osLogEnt (L := L) x e := by
  unfold osLogEnt gElem
  letI := (gooseOsGS (L := L)).osAllG
  exact ghostMapElem_persist _ _ _ _

/-- The claims a step is shown: what they know of the state, and their entries in the authority. -/
theorem claims_info {st : OsState} {Γn : GMap (Ino × NameSet) NamesH}
    (hcoh : NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn) :
    ∀ cl : List ClaimW, (∀ c ∈ cl, c.2.1 ≠ .only []) →
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      ⌜(∀ c ∈ cl, ∀ b, c.2.1.Mem b → st.tree.entry c.1 b = c.2.2.1.cur !! b) ∧
        ∀ c ∈ cl, Γn !! (c.1, c.2.1) = some c.2.2.1 ∧
        c.2.2.1 = namesOf (st.fs.treeDur, st.fs.metaLog) c.1 c.2.1⌝
  | [], _ => by
    iintro _ _
    ipureintro
    exact ⟨fun c hc => by simp at hc, fun c hc => by simp at hc⟩
  | c :: cl, hne => by
    iintro HA Hl
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨H, Hl⟩
    icases claims_info hcoh cl (fun c' h => hne c' (List.mem_cons_of_mem _ h)) $$ HA Hl with %ih
    icases osNames_entry hcoh c.1 c.2.1 _ c.2.2.1 $$ HA H with %he
    icases osNames_auth L hcoh c.1 c.2.1 _ c.2.2.1 $$ HA H with %hh
    rw [osNames_of_ne _ _ (hne c (by simp))]
    icases gAuth_lookup _ _ _ _ _ _ $$ HA H with %hl
    ipureintro
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · exact he
      · exact ih.1 c' hc'
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨hl, hh⟩
      · exact ih.2 c' hc'

/-- The claims a step wrote, updated in the authority. -/
theorem claims_upd (V' : Hist) (f : ClaimW → NamesH) :
    ∀ (cl : List ClaimW) (Γn : GMap (Ino × NameSet) NamesH),
    (∀ c ∈ cl, c.2.1 ≠ .only []) → (∀ c ∈ cl, f c = namesOf V' c.1 c.2.1) →
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn
          (insKeys V' (cl.map (fun c => (c.1, c.2.1))) Γn) ∗
        [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) (f c)
  | [], Γn, _, _ => by
    iintro HA -
    imodintro
    isplitl [HA]
    · rw [show insKeys V' (([] : List ClaimW).map (fun c => (c.1, c.2.1))) Γn = Γn from rfl]
      iexact HA
    · iapply (BigSepL.bigSepL_nil).2; iempintro
  | c :: cl, Γn, hne, hf => by
    iintro HA Hl
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨H, Hl⟩
    imod claims_upd V' f cl Γn (fun c' h => hne c' (List.mem_cons_of_mem _ h))
      (fun c' h => hf c' (List.mem_cons_of_mem _ h)) $$ HA Hl with ⟨HA, Hl⟩
    rw [osNames_of_ne _ _ (hne c (by simp))]
    imod gAuth_update _ _ _ _ _ (namesOf V' c.1 c.2.1) $$ HA H with ⟨HA, H⟩
    imodintro
    isplitl [HA]
    · rw [show insKeys V' ((c :: cl).map (fun c => (c.1, c.2.1))) Γn =
          <[(c.1, c.2.1) := namesOf V' c.1 c.2.1]> (insKeys V' (cl.map (fun c => (c.1, c.2.1))) Γn)
          from rfl]
      iexact HA
    · iapply (BigSepL.bigSepL_cons).2
      isplitl [H]
      · rw [osNames_of_ne _ _ (hne c (by simp)), hf c (by simp)]; iexact H
      · iexact Hl

/-- The calls in flight other than `k`, each with its fraction of the permission, and `k`'s:
neither is the whole permission. -/
theorem callResS_excl (Γc : GMap Nat (Nat × Qp)) (k : Nat) (x0 : Nat × Qp) (hk : Γc !! k = some x0) :
    ⊢ callResS (gooseOsGS (L := L)) Γc -∗
      ⌜∀ t x, t ≠ k → Γc !! t = some x → x.2.val < 1 ∧ x0.2.val < 1⌝ ∗
        callResS (gooseOsGS (L := L)) Γc := by
  iintro H
  by_cases hP : ∀ t x, t ≠ k → Γc !! t = some x → x.2.val < 1 ∧ x0.2.val < 1
  · isplitr
    · ipureintro; exact hP
    · iexact H
  · have : ∃ t x, t ≠ k ∧ Γc !! t = some x ∧ ¬ (x.2.val < 1 ∧ x0.2.val < 1) :=
      Classical.byContradiction fun hn => hP fun t x hne ht =>
        Classical.byContradiction fun hv => hn ⟨t, x, hne, ht, hv⟩
    obtain ⟨t, x, hne, ht, hv⟩ := this
    unfold callResS
    icases (BigSepM.bigSepM_delete (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : Nat × Qp) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ H
      with ⟨Hq, H⟩
    have ht' : (GMap.delete k Γc) !! t = some x := by
      rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact ht
    icases (BigSepM.bigSepM_lookup (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : Nat × Qp) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) ht') $$ H
      with Ht
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hq Ht with %Hv
    exact absurd ⟨DFrac.valid_op_own Hv.1, DFrac.valid_own_op Hv.1⟩ hv

end ghost

theorem namesOf_newDir_cur (V : Hist) (j : Ino) (b : GoString) (J : Ino) (s0 : Nat) :
    (namesOf (V.1, V.2 ++ [⟨.mkdir j b J, s0⟩]) J (.except [])).cur = ∅ := by
  show restrictN (.except []) (entsOf (Hist.now (V.1, V.2 ++ [⟨.mkdir j b J, s0⟩])) J) = ∅
  rw [hist_now_snoc]
  apply GMap.ext; intro c
  show restrictN (.except []) (entsOf ((MetaOp.mkdir j b J).apply V.now) J) !! c = (∅ : Ents) !! c
  rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), entsOf_lookup]
  simp [MetaOp.apply, Tree.entry, GMap.lookup_insert]

open Classical in
theorem namesOf_newDir_next (V : Hist) (j : Ino) (b : GoString) (J : Ino) (s0 : Nat) :
    (namesOf (V.1, V.2 ++ [⟨.mkdir j b J, s0⟩]) J (.except [])).next = V.2.length + 1 := by
  rw [namesOf_next]
  simp only [List.length_append, List.length_singleton]
  rw [lastSat_succ, if_pos]
  apply decide_eq_true
  exact ⟨⟨.mkdir j b J, s0⟩, by simp, [], by simp [NameSet.Mem], .inr ⟨j, b, rfl⟩⟩

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **A step that logs `o` for the call `k`** (or only ends it), the claims `cl` (whole) written:
from what it finds of the state (`P`, given by the caller's resources `F` through the claims'
authority; `ClaimsAt`: what the claims know) and what it returns (`W w logged`). The obligations:
each claim is written and every slot `o` writes is in one; the claims' `next` bound the call's
start (or the call holds the whole permission); a directory operation holds the whole permission;
the tree after `o` is well formed, names no new file, has the old directories and the new ones
(fresh), `o` is applicable if a file operation, and the claims' entries after `o` are as given. -/
theorem wp_logStepS (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat)
    (q : Qp) (o : MetaOp) (cl : List ClaimW) (F : IProp GF) (P : OsState → Prop)
    (W : val → Bool → Prop)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ o.Writes c.1 b)
    (hslots : ∀ sl ∈ o.slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ q = 1)
    (hdir : o.IsDirOp → q = 1)
    (hadd : ∀ j b, b ∈ o.adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧ W w true)))
    (htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallS (L := L) k s0 q -∗
      (∀ w, osCallPerm (L := L) q -∗ F -∗
        ((⌜W w false⌝ ∗ [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ x, osLogged (L := L) x ⟨o, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨o, s0⟩ c.2.2.2)) ∗
           [∗list] J ∈ o.newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_fs_stepM op _ Φ hv hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iexfalso; iapply legacy_callS_excl st k s0 q $$ Hk Hm
  unfold treeShared
  icases Hm with ⟨%V0, %s1, %Γdf, %Γc, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  icases hF st Γn hR hcoh.2 $$ HAn HF with %hP
  icases claims_info hcoh.2 cl hne $$ HAn Hcl with %hci
  obtain ⟨hat0, hlk⟩ := hci
  have hat : ClaimsAt st cl := by
    refine ⟨hat0, fun c hc b hb => ?_, fun c hc c' hc' hj hN b hb hb' => ?_⟩
    · rw [(hlk c hc).2]
      exact restrictN_lookup_not _ _ _ hb
    · have h2 := (hlk c' hc').1
      rw [← hj] at h2
      exact hcoh.2.disj c.1 c.2.1 c'.2.1 _ _ b (hlk c hc).1 h2 hN hb hb'
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by
    have := hc.calls k; rw [hk] at this; exact this.symm
  icases callResS_excl Γc k (s0, q) hk $$ Hcr with ⟨%hexcl, Hcr⟩
  have hsole : q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k := by
    intro hq k' s' hk'
    refine Classical.byContradiction fun hne => ?_
    have h1 := hc.calls k'
    rw [hk'] at h1
    cases hx : Γc !! k' with
    | none => rw [hx] at h1; cases h1
    | some x =>
      have := (hexcl k' x hne hx).2
      rw [hq] at this; exact absurd this (by simp)
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (E \ ↑osN) \ ↑osShN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', st', hst, hfs⟩ := hprog st hw hR hcall hsole hP hat
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 hfs Hag
    exact ⟨e', h, st', hst, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  obtain ⟨w, rfl, hres⟩ := hpost st e' st' hw hR hcall hsole hP hat Hst
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  rcases hres with ⟨rfl, hW⟩ | ⟨hlf, hlt, hW⟩
  · -- no effect: the call ended
    have hs : FilesSame st (st.metaEnd k) := filesSame_metaEnd st k
    imod osWorld_filesSame (st := st) (st' := st.metaEnd k) hs Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imod Hclose $$ [Hs HAn Halen HAlog] with -
    · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd k)
          (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [OsState.metaEnd]
      try unfold treeShared
      iexists V0, s1, Γdf, GMap.delete k Γc
      iframe
      ipureintro; exact ⟨fsTreeWf_metaEnd hw k, treeCohS_metaEnd hc k⟩
    iapply wp_value'
    iapply HΦ $$ %w [Hq] HF
    · unfold osCallPerm; iexact Hq
    ileft
    isplitr
    · ipureintro; exact hW
    · iexact Hcl
  · -- logged
    obtain ⟨htw, hnm, hdirs, hnew, hok, hcur⟩ := htree st hw hR hP hat
    have htr := hlf.tree
    have hwf' : FsTreeWf st' := hlf.wf hw (hR ▸ htw) hnm hlt
    have hpss : ∀ y (ey : LogEntry), st.fs.metaLog[y]? = some ey →
        (∃ sl ∈ o.slots, sl ∈ ey.op.slots) → y < s0 := by
      rintro y ey hy ⟨sl, hsl, hsl'⟩
      obtain ⟨c, hcm, hc1, hc2⟩ := hslots sl hsl
      have hlt' : y < c.2.2.1.next := by
        rw [(hlk c hcm).2]
        refine lt_namesOf_next hy hc2 (.inl ?_)
        rw [hc1]; exact hsl'
      rcases hnext c hcm with hn | hq1
      · omega
      · have := hc.whole k _ hk hq1
        have := (List.getElem?_eq_some_iff.1 hy).1
        simp only at *; omega
    have hcoh' : TreeCohS st' s1 Γdf (GMap.delete k Γc) :=
      treeCohS_log hc hk o hlf.dur hlf.log hlf.dfds hlf.calls htr hpss hdir hexcl hok hadd
    have hnc := namesCoh_log hcoh.2 ⟨o, s0⟩ (cl.map (fun c => (c.1, c.2.1)))
      (fun kk hkk => by
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hkk
        exact ⟨_, (hlk c hcm).1⟩)
      (fun sl hsl => by
        obtain ⟨c, hcm, hc1, hc2⟩ := hslots sl hsl
        exact ⟨(c.1, c.2.1), List.mem_map.2 ⟨c, hcm, rfl⟩, hc1, hc2⟩)
      hnew hdirs
    have hcl' : ∀ c ∈ cl, c.2.2.1.log st.fs.metaLog.length ⟨o, s0⟩ c.2.2.2 =
        namesOf (st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩]) c.1 c.2.1 := by
      intro c hcm
      have hsw := namesOf_snoc_written (st.fs.treeDur, st.fs.metaLog) ⟨o, s0⟩ c.1 c.2.1 (hwr c hcm)
      simp only at hsw
      rw [hsw, ← (hlk c hcm).2]
      congr 1
      exact (hcur c hcm).symm
    -- ghost updates
    imod gAuth_update _ _ _ _ _ (st.fs.roots, ((st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩]) : Hist))
      $$ Has Hs with ⟨Has, Hs⟩
    imod (letI := (gooseOsGS (L := L)).osAllG;
      mono_nat_own_update (γ := (gooseOsGS (L := L)).γlen)
        (st.fs.metaLog ++ [(⟨o, s0⟩ : LogEntry)]).length (by simp)) $$ Halen with ⟨Halen, #Hlb⟩
    imod gAuth_insert _ _ _ st.fs.metaLog.length (⟨o, s0⟩ : LogEntry)
      (by rw [logMap_lookup]; simp) $$ HAlog with ⟨HAlog, Hent⟩
    imod logEnt_persist _ _ $$ Hent with #Hent
    imod claims_upd (st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩])
      (fun c => c.2.2.1.log st.fs.metaLog.length ⟨o, s0⟩ c.2.2.2) cl Γn hne hcl' $$ HAn Hcl
      with ⟨HAn, Hcl⟩
    imod osWorld_filesSame (st := st) (st' := st') hlf.same Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    have hlen : (st.fs.metaLog ++ [(⟨o, s0⟩ : LogEntry)]).length = st.fs.metaLog.length + 1 := by
      simp
    have hle : s0 ≤ st.fs.metaLog.length := hc.callsLe k _ hk
    rw [histMap_insert, show logMap (st.fs.treeDur, st.fs.metaLog).2 = logMap st.fs.metaLog from rfl,
      ← logMap_snoc]
    have hkey : ∀ J, J ∉ st.tree →
        insKeys (st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩]) (cl.map (fun c => (c.1, c.2.1))) Γn !!
          (J, .except []) = none := by
      intro J hJ
      rw [insKeys_lookup]
      split
      · rename_i hm
        obtain ⟨c, hcm, hce⟩ := List.mem_map.1 hm
        simp only [Prod.mk.injEq] at hce
        have := hcoh.2.dirs _ _ _ (hlk c hcm).1
        rw [hce.1] at this
        exact absurd this hJ
      · cases hl : Γn !! (J, NameSet.except []) with
        | none => rfl
        | some h0 => exact absurd (hcoh.2.dirs _ _ _ hl) hJ
    rcases newDirs_cases o with hnd | ⟨j0, b0, J, rfl, hnd⟩
    · have hΓ : insKeys (st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩])
          (newKeys o ++ cl.map (fun c => (c.1, c.2.1))) Γn =
          insKeys (st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩]) (cl.map (fun c => (c.1, c.2.1))) Γn := by
        simp [newKeys, hnd]
      rw [hΓ] at hnc
      imod Hclose $$ [Hs HAn Halen HAlog] with -
      · inext
        iexists (st.fs.treeDur, st.fs.metaLog ++ [⟨o, s0⟩]), _
        isplitl [Hs]
        · rw [← hR]; iexact Hs
        iframe
        ipureintro; exact ⟨hcoh.1, hnc⟩
      imodintro
      iexists Γb, Γm, Γf, Γt
      isplitl [Hw]
      · unfold osWorld; iexact Hw
      isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
      · isplitr [Hcm]
        rotate_left
        · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st')
            (commitGrows_of_eq hlf.committed) $$ Hcm
        iright
        iexists V0, s1, Γdf, GMap.delete k Γc
        rw [hlf.roots, hlf.dur, hlf.log]
        iframe
        ipureintro; exact ⟨hwf', hcoh'⟩
      iapply wp_value'
      iapply HΦ $$ %w [Hq] HF
      · unfold osCallPerm; iexact Hq
      iright
      isplitr
      · ipureintro; exact hW
      iexists st.fs.metaLog.length
      isplitr [Hcl]
      · unfold osLogged
        isplitr
        · ipureintro; exact hle
        isplitr
        · iexact Hent
        · unfold osLogLb
          iapply (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_le _ (Nat.le_of_eq hlen.symm)) $$ Hlb
      isplitl [Hcl]
      · iexact Hcl
      rw [hnd]; iapply (BigSepL.bigSepL_nil).2; iempintro
    · have hΓ : insKeys (st.fs.treeDur, st.fs.metaLog ++ [⟨.mkdir j0 b0 J, s0⟩])
          (newKeys (.mkdir j0 b0 J) ++ cl.map (fun c => (c.1, c.2.1))) Γn =
          <[(J, .except []) := namesOf (st.fs.treeDur, st.fs.metaLog ++ [⟨.mkdir j0 b0 J, s0⟩]) J
            (.except [])]> (insKeys (st.fs.treeDur, st.fs.metaLog ++ [⟨.mkdir j0 b0 J, s0⟩])
              (cl.map (fun c => (c.1, c.2.1))) Γn) := rfl
      rw [hΓ] at hnc
      imod gAuth_insert _ _ _ (J, NameSet.except [])
        (namesOf (st.fs.treeDur, st.fs.metaLog ++ [⟨.mkdir j0 b0 J, s0⟩]) J (.except []))
        (hkey J (hnew J (by simp [hnd]))) $$ HAn with ⟨HAn, HJ⟩
      imod Hclose $$ [Hs HAn Halen HAlog] with -
      · inext
        iexists (st.fs.treeDur, st.fs.metaLog ++ [⟨.mkdir j0 b0 J, s0⟩]), _
        isplitl [Hs]
        · rw [← hR]; iexact Hs
        iframe
        ipureintro; exact ⟨hcoh.1, hnc⟩
      imodintro
      iexists Γb, Γm, Γf, Γt
      isplitl [Hw]
      · unfold osWorld; iexact Hw
      isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
      · isplitr [Hcm]
        rotate_left
        · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st')
            (commitGrows_of_eq hlf.committed) $$ Hcm
        iright
        iexists V0, s1, Γdf, GMap.delete k Γc
        rw [hlf.roots, hlf.dur, hlf.log]
        iframe
        ipureintro; exact ⟨hwf', hcoh'⟩
      iapply wp_value'
      iapply HΦ $$ %w [Hq] HF
      · unfold osCallPerm; iexact Hq
      iright
      isplitr
      · ipureintro; exact hW
      iexists st.fs.metaLog.length
      isplitr [Hcl HJ]
      · unfold osLogged
        isplitr
        · ipureintro; exact hle
        isplitr
        · iexact Hent
        · unfold osLogLb
          iapply (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_le _ (Nat.le_of_eq hlen.symm)) $$ Hlb
      isplitl [Hcl]
      · iexact Hcl
      rw [hnd]
      iapply (BigSepL.bigSepL_cons).2
      isplitl [HJ]
      · iexists namesOf (st.fs.treeDur, st.fs.metaLog ++ [⟨.mkdir j0 b0 J, s0⟩]) J (.except [])
        rw [osNames_except]
        isplitl [HJ]
        · iexact HJ
        · ipureintro
          exact ⟨namesOf_newDir_cur (st.fs.treeDur, st.fs.metaLog) j0 b0 J s0,
            namesOf_newDir_next (st.fs.treeDur, st.fs.metaLog) j0 b0 J s0⟩
      · iapply (BigSepL.bigSepL_nil).2; iempintro

end specs

end Fs
end Perennial

end
