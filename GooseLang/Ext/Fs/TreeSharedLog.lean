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

/-- A directory with an entry is one of the tree. -/
theorem mem_of_entry {m : Tree} {j : Ino} {b : GoString} {n : Node} (h : m.entry j b = some n) :
    j ∈ m := by
  cases hj : m !! j with
  | none => simp [Tree.entry, hj] at h
  | some _ => rw [GMap.mem_iff, hj]; rfl

/-- An operation writes its directory. -/
theorem writes_dir (o : MetaOp) : ∃ b, o.Writes o.dir b := by
  cases o with
  | create j b i => exact ⟨b, .inl (by simp [MetaOp.slots, MetaOp.dir])⟩
  | mkdir j b J => exact ⟨b, .inl (by simp [MetaOp.slots, MetaOp.dir])⟩
  | remove j b n => exact ⟨b, .inl (by simp [MetaOp.slots, MetaOp.dir])⟩
  | rename j b j' b' n old => exact ⟨b, .inl (by simp [MetaOp.slots, MetaOp.dir])⟩

/-- A walk from a directory reachable from `ri` ends at one reachable from `ri`. -/
theorem reachFrom_walk {m : Tree} {ri : Ino} : ∀ {cs : List GoString} {j x : Ino},
    ReachFrom m ri j → walk m (.dir j) cs = some (.dir x) → ReachFrom m ri x
  | [], j, x, hj, h => by simp [walk] at h; subst h; exact hj
  | c :: cs, j, x, hj, h => by
    simp only [walk] at h
    cases he : m.entry j c with
    | none => rw [he] at h; cases h
    | some n =>
      rw [he] at h; simp only at h
      cases n with
      | dir j' => exact reachFrom_walk (.child j c j' hj he) h
      | file i => cases cs <;> simp [walk] at h

/-- **A directory a path names is reachable from the root the path is under** (and so are the
path's children). -/
theorem reachFrom_of_lookup {st : OsState} {d : GoString} {j : Ino}
    (h : st.lookup d = some (.dir j)) :
    ∃ rj ∈ st.fs.roots, IsUnder rj.1 d ∧ (∀ b, IsUnder rj.1 (child d b)) ∧
      ReachFrom st.tree rj.2 j := by
  obtain ⟨r, j0, cs, hrj, -, rfl, hw⟩ := lookup_some h
  exact ⟨(r, j0), hrj, isUnder_joinPath _ _,
    fun b => by rw [← joinPath_snoc]; exact isUnder_joinPath _ _, reachFrom_walk .root hw⟩

/-- An operation's directory is one of its slots'. -/
theorem dir_mem_slots (o : MetaOp) : ∃ b, (o.dir, b) ∈ o.slots := by
  cases o with
  | create j b i => exact ⟨b, by simp [MetaOp.slots, MetaOp.dir]⟩
  | mkdir j b J => exact ⟨b, by simp [MetaOp.slots, MetaOp.dir]⟩
  | remove j b n => exact ⟨b, by simp [MetaOp.slots, MetaOp.dir]⟩
  | rename j b j' b' n old => exact ⟨b, by simp [MetaOp.slots, MetaOp.dir]⟩

/-- The directories of an earlier tree of the run are directories of a later one. -/
theorem prefTree_mono_mem (T0 : Tree) (log : List LogEntry) {t : Nat} :
    ∀ u, t ≤ u → u ≤ log.length → ∀ x, x ∈ prefTree T0 log t → x ∈ prefTree T0 log u
  | 0, h, _, x, hx => by rwa [show t = 0 by omega] at hx
  | u + 1, h, hu, x, hx => by
    rcases Nat.lt_or_ge u t with h' | h'
    · rwa [show t = u + 1 by omega] at hx
    obtain ⟨e, he⟩ : ∃ e, log[u]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [prefTree_succ T0 log he]
    exact mem_apply_of_mem _ _ _ (prefTree_mono_mem T0 log u h' (by omega) x hx)

/-- An operation whose written directories are all of one root keeps a tree's entries naming
directories in their parents' roots. -/
theorem ents_apply {ρ : Ino → GoString} {m : Tree} (o : MetaOp)
    (hm : ∀ j b J, m.entry j b = some (.dir J) → ρ J = ρ j)
    (htag : ∀ j b, o.Writes j b → ρ j = ρ o.dir) :
    ∀ j b J, (o.apply m).entry j b = some (.dir J) → ρ J = ρ j := by
  intro j b J h
  cases o with
  | create j0 b0 i =>
    rw [entry_create] at h
    split at h
    · simp at h
    · exact hm j b J h
  | mkdir j0 b0 J0 =>
    rw [entry_mkdir] at h
    split at h
    · simp at h
    split at h
    · rename_i hjb
      obtain ⟨rfl, rfl⟩ := hjb
      cases h
      rw [htag J b0 (.inr ⟨j0, b0, rfl⟩), htag j0 b0 (.inl (by simp [MetaOp.slots]))]
    · exact hm j b J h
  | remove j0 b0 n =>
    rw [entry_remove] at h
    split at h
    · simp at h
    · exact hm j b J h
  | rename j0 b0 j1 b1 n old =>
    rw [entry_rename] at h
    cases hs : m.entry j0 b0 with
    | none => rw [hs] at h; exact hm j b J h
    | some n' =>
      rw [hs] at h; simp only at h
      split at h
      · rename_i hjb
        obtain ⟨rfl, rfl⟩ := hjb
        cases h
        rw [hm j0 b0 J hs, htag j0 b0 (.inl (by simp [MetaOp.slots])),
          htag j1 b1 (.inl (by simp [MetaOp.slots]))]
      · split at h
        · simp at h
        · exact hm j b J h

/-- **The shared coherence after a step that logged `o`** for the call `k` (begun at `s0`, holding
`q` of the permission). -/
theorem treeCohS_log {st st' : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) {k s0 : Nat} {pc : GoString} {q : Qp}
    (hk : Γc !! k = some ((s0, pc), q)) (o : MetaOp)
    (hdur : st'.fs.treeDur = st.fs.treeDur)
    (hlog : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s0⟩])
    (hdf : st'.proc.dfds = GMap.fmap (·.note o) st.proc.dfds)
    (hca : st'.proc.calls = GMap.delete k st.proc.calls)
    (htree : st'.tree = o.apply st.tree)
    (hpss : ∀ y (ey : LogEntry), st.fs.metaLog[y]? = some ey →
      (∃ sl ∈ o.slots, sl ∈ ey.op.slots) → y < s0)
    (hdirK : o.IsDirOp → ∀ ρ, RootCoh st ρ → CallsK st ρ Γc Γg → ∀ y (ey : LogEntry), s0 ≤ y →
      st.fs.metaLog[y]? = some ey → tagOf ρ ey ≠ callKey st.fs.roots pc)
    (hexcl : ∀ t x, t ≠ k → Γc !! t = some x → callKey st.fs.roots x.1.2 = callKey st.fs.roots pc →
      x.2.val < 1 ∧ ¬ o.IsDirOp)
    (hval : ∀ c x t g, c ≠ k → Γc !! c = some x → Γg !! t = some g →
      callKey st.fs.roots x.1.2 = callKey st.fs.roots pc → callKey st.fs.roots g.1.2 = callKey st.fs.roots pc →
      x.2.val + q.val + g.2.val ≤ 1)
    (hok : ¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
      t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i)
    (hadd : ∀ j b, b ∈ o.adds j → NameOk b)
    (hw : FsTreeWf st) (hroots : st'.fs.roots = st.fs.roots)
    (hρ : ∀ ρ, RootCoh st ρ → ∃ ρ' : Ino → GoString, (∀ j, j ∈ st.tree → ρ' j = ρ j) ∧
      (∀ j b, o.Writes j b → ρ' j = ρ' o.dir) ∧ (∀ j b, o.Writes j b → j ∈ o.apply st.tree) ∧
      ρ' o.dir = callKey st.fs.roots pc) :
    TreeCohS st' Γdf (GMap.delete k Γc) Γg := by
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
  · obtain ⟨ρ, hrc, hck⟩ := hc.rc
    obtain ⟨ρ', hag, htag, hwk, hkey⟩ := hρ ρ hrc
    have hpt : prefTree st.fs.treeDur st.fs.metaLog st.fs.metaLog.length = st.tree := (tree_prefTree st).symm
    have htrees : ∀ t, t ≤ st.fs.metaLog.length → ∀ x, x ∈ prefTree st.fs.treeDur st.fs.metaLog t →
        x ∈ st.tree := fun t ht x hx => hpt ▸ prefTree_mono_mem _ _ _ ht (Nat.le_refl _) x hx
    have htg : ∀ x (e : LogEntry), 0 ≤ x → st.fs.metaLog[x]? = some e → tagOf ρ' e = tagOf ρ e :=
      fun x e _ he => by
        obtain ⟨b, hb⟩ := writes_dir e.op
        exact hag _ (hrc.wkeys x e he _ b hb)
    have hs1 : 0 ≤ st.fs.metaLog.length := Nat.zero_le _
    -- the legacy entries and the old directory operations took effect before the new entry's call
    have haft : ∀ y (ey : LogEntry), st.fs.metaLog[y]? = some ey →
        ((ey.op.IsDirOp ∧ tagOf ρ ey = callKey st.fs.roots pc) ∨ y < 0) → y < s0 :=
      fun y ey hy hd => hd.elim (hck.after k _ hk y ey hy) (fun h => absurd h (Nat.not_lt_zero _))
    -- an entry at or after a call's start is not of the legacy prefix
    have hge : ∀ t x y (ey : LogEntry), Γc !! t = some x → x.1.1 ≤ y → st.fs.metaLog[y]? = some ey →
        0 ≤ y := fun _ _ _ _ _ _ _ => Nat.zero_le _
    have hnew : tagOf ρ' (⟨o, s0⟩ : LogEntry) = callKey st.fs.roots pc := hkey
    refine ⟨ρ', ⟨⟨fun r j hr => ?_, fun t ht1 ht2 j b J he => ?_, fun x e hx he j b hwr => ?_⟩,
      fun x ex hx => ?_, fun x e he j b hwr => ?_⟩, ?_⟩
    · rw [hroots] at hr
      have hj0 : j ∈ prefTree st.fs.treeDur st.fs.metaLog st.fs.metaLog.length :=
        (hw.hist st.fs.metaLog.length (Nat.le_refl _)).1.1 j (.root r j hr)
      have hjt : j ∈ st.tree := by rw [hpt] at hj0; exact hj0
      rw [hag j hjt]; exact hrc.tags.roots r j hr
    · rw [hlog, hdur] at he
      rw [hlog] at ht2
      simp only [List.length_append, List.length_singleton] at ht2
      rcases Nat.lt_or_ge t (st.fs.metaLog.length + 1) with h | h
      · rw [prefTree_snoc_le _ _ _ (by omega)] at he
        have hwt := (hw.hist t (by omega)).1
        have hJ : J ∈ prefTree st.fs.treeDur st.fs.metaLog t :=
          (hwt.2.2.1 j b (.dir J) he).2 J (by simp [Node.dirIno])
        rw [hag J (htrees t (by omega) J hJ), hag j (htrees t (by omega) j (mem_of_entry he))]
        exact hrc.tags.ents t ht1 (by omega) j b J he
      · have he' : (st.fs.metaLog ++ [(⟨o, s0⟩ : LogEntry)])[st.fs.metaLog.length]? = some ⟨o, s0⟩ := by simp
        rw [show t = st.fs.metaLog.length + 1 by omega, prefTree_succ _ _ he',
          prefTree_snoc_le _ _ _ (Nat.le_refl _), hpt] at he
        have hcur : ∀ j b J, st.tree.entry j b = some (.dir J) → ρ' J = ρ' j := by
          intro j b J he
          have hwt := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).1
          rw [← hpt] at he
          have hJ := (hwt.2.2.1 j b (.dir J) he).2 J (by simp [Node.dirIno])
          rw [hag J (htrees _ (Nat.le_refl _) J hJ), hag j (htrees _ (Nat.le_refl _) j (mem_of_entry he))]
          exact hrc.tags.ents _ hs1 (Nat.le_refl _) j b J he
        exact ents_apply o hcur htag j b J he
    · rw [hlog] at he
      rcases getElem?_snoc_cases he with ⟨-, he⟩ | ⟨rfl, rfl⟩
      · rw [htg x e hx he, hag j (hrc.wkeys x e he j b hwr)]
        exact hrc.tags.ops x e hx he j b hwr
      · exact htag j b hwr
    · rw [hlog] at hx
      rcases getElem?_snoc_cases hx with ⟨hxl, hx⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hl1, hl2⟩ := hrc.dox x ex hx
        refine ⟨fun hxs => ⟨(hl1 hxs).1, fun z ez hxz hz => ?_⟩, fun hd => ?_⟩
        · rw [hlog] at hz
          rcases getElem?_snoc_cases hz with ⟨-, hz⟩ | ⟨rfl, rfl⟩
          · exact (hl1 hxs).2 z ez hxz hz
          · exact haft x ex hx (.inr hxs)
        · rcases Nat.lt_or_ge x 0 with hxs | hxs
          · refine ⟨fun y ey h1 h2 _ => absurd h1 (by rw [(hl1 hxs).1]; omega), fun z ez hxz hz _ => ?_⟩
            rw [hlog] at hz
            rcases getElem?_snoc_cases hz with ⟨-, hz⟩ | ⟨rfl, rfl⟩
            · exact (hl1 hxs).2 z ez hxz hz
            · exact haft x ex hx (.inr hxs)
          · obtain ⟨hA, hB⟩ := hl2 hd
            refine ⟨fun y ey h1 h2 hy => ?_, fun z ez hxz hz hzt => ?_⟩
            · rw [hlog] at hy
              rcases getElem?_snoc_cases hy with ⟨-, hy⟩ | ⟨rfl, -⟩
              · rcases Nat.lt_or_ge y 0 with hys | hys
                · exact absurd h1 (Nat.not_le.2 (((hrc.dox y ey hy).1 hys).2 x ex h2 hx))
                · rw [htg y ey hys hy, htg x ex hxs hx]; exact hA y ey h1 h2 hy
              · omega
            · rw [hlog] at hz
              rcases getElem?_snoc_cases hz with ⟨hzl, hz⟩ | ⟨rfl, rfl⟩
              · have hzs : 0 ≤ z := Nat.zero_le _
                rw [htg z ez hzs hz, htg x ex hxs hx] at hzt
                exact hB z ez hxz hz hzt
              · rw [hnew, htg x ex hxs hx] at hzt
                exact haft x ex hx (.inl ⟨hd, hzt.symm⟩)
      · refine ⟨fun hxs => absurd hxs (by omega), fun hd => ⟨fun y ey h1 h2 hy => ?_, fun z ez hxz hz _ => ?_⟩⟩
        · simp only at h1
          rw [hlog] at hy
          rcases getElem?_snoc_cases hy with ⟨-, hy⟩ | ⟨rfl, -⟩
          · have hys : 0 ≤ y := hge k _ y ey hk h1 hy
            rw [htg y ey hys hy, hnew]
            exact hdirK hd ρ hrc hck y ey h1 hy
          · omega
        rw [hlog] at hz
        have := (List.getElem?_eq_some_iff.1 hz).1
        simp at this; omega
    · rw [hlog] at he
      rw [htree]
      rcases getElem?_snoc_cases he with ⟨-, he⟩ | ⟨rfl, rfl⟩
      · exact mem_apply_of_mem _ _ _ (hrc.wkeys x e he j b hwr)
      · exact hwk j b hwr
    · -- the calls' part, per key
      have hlk : ∀ t x, (GMap.delete k Γc) !! t = some x → t ≠ k ∧ Γc !! t = some x := by
        intro t x hx
        by_cases h0 : k = t
        · subst h0; simp at hx
        · rw [GMap.lookup_delete_ne _ h0] at hx; exact ⟨Ne.symm h0, hx⟩
      refine ⟨fun t x hx hq y ey hy he => ?_, fun t x hx y ey he hd => ?_,
        fun c x t g hx hg hkg hq hle y ey hy he => ?_⟩
      · obtain ⟨hne, hx⟩ := hlk t x hx
        rw [hroots]
        rw [hlog] at he
        rcases getElem?_snoc_cases he with ⟨-, he⟩ | ⟨rfl, rfl⟩
        · rw [htg y ey (hge t x y ey hx hy he) he]; exact hck.whole t x hx hq y ey hy he
        · rw [hnew]; intro heq
          have := (hexcl t x hne hx heq.symm).1
          rw [hq] at this; exact absurd this (by simp)
      · obtain ⟨hne, hx⟩ := hlk t x hx
        rw [hroots] at hd
        rw [hlog] at he
        rcases getElem?_snoc_cases he with ⟨-, he⟩ | ⟨rfl, rfl⟩
        · obtain ⟨hd1, hd2⟩ := hd
          rw [htg y ey (Nat.zero_le _) he] at hd2; exact hck.after t x hx y ey he ⟨hd1, hd2⟩
        · obtain ⟨hd1, hd2⟩ := hd
          rw [hnew] at hd2; exact absurd hd1 (hexcl t x hne hx hd2.symm).2
      · obtain ⟨hne, hx⟩ := hlk c x hx
        rw [hroots] at hkg ⊢
        rw [hlog] at he
        rcases getElem?_snoc_cases he with ⟨-, he⟩ | ⟨rfl, rfl⟩
        · rw [htg y ey (hge c x y ey hx hy he) he]; exact hck.pair c x t g hx hg hkg hq hle y ey hy he
        · rw [hnew]; intro heq
          have h1 := hval c x t g hne hx hg heq.symm (hkg.trans heq.symm)
          have h2 := q.2
          exfalso; grind
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
  · intro t x hx
    rw [hca]
    by_cases h0 : k = t
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; rw [GMap.lookup_delete_ne _ h0]; exact hc.calls t x hx
  · intro t x hx
    by_cases h0 : k = t
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx
      rw [hlog]; simp; have := hc.callsLe t x hx; omega
  · intro t x hx
    rw [hca]
    by_cases h0 : k = t
    · subst h0; have := hc.gdisj k x hx; rw [hk] at this; cases this
    · rw [GMap.lookup_delete_ne _ h0]; exact hc.gcalls t x hx
  · intro t x hx
    by_cases h0 : k = t
    · subst h0; simp
    · rw [GMap.lookup_delete_ne _ h0]; exact hc.gdisj t x hx
  · intro t s hs
    rw [hca] at hs
    by_cases h0 : k = t
    · subst h0; simp at hs
    · rw [GMap.lookup_delete_ne _ h0] at hs; rw [GMap.lookup_delete_ne _ h0]; exact hc.cover t s hs

/-- The call `k` on `pc` (begun at `s0`, holding `q`) holds the whole permission (`gd = none`), or
the rest of it beside the guard `gd` of the same key (begun no later). -/
def WholeG (R : Roots) (pc : GoString) (q : Qp) (s0 : Nat) : Option (Nat × CallV) → Prop
  | none => q = 1
  | some (_, (sg, pg), g) => q.val + g.val = 1 ∧ sg ≤ s0 ∧ callKey R pg = callKey R pc

/-- A call holding the whole permission, or the rest of it beside a guard of its key begun no
later, began after every entry of its key, and no other logging call of its key is in flight. -/
theorem wholeG_facts {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) {k s0 : Nat} {pc : GoString} {q : Qp}
    (hk : Γc !! k = some ((s0, pc), q)) {gd : Option (Nat × CallV)}
    (hexcl : ∀ t x, t ≠ k → Γc !! t = some x → callKey st.fs.roots x.1.2 = callKey st.fs.roots pc →
      x.2.val < 1 ∧ q.val < 1)
    (hval : ∀ c x t g, c ≠ k → Γc !! c = some x → Γg !! t = some g →
      callKey st.fs.roots x.1.2 = callKey st.fs.roots pc →
      callKey st.fs.roots g.1.2 = callKey st.fs.roots pc → x.2.val + q.val + g.2.val ≤ 1)
    (hgd : ∀ t x, gd = some (t, x) → Γg !! t = some x)
    (hw : WholeG st.fs.roots pc q s0 gd) :
    (∀ ρ, RootCoh st ρ → CallsK st ρ Γc Γg → ∀ y (ey : LogEntry), s0 ≤ y →
      st.fs.metaLog[y]? = some ey → tagOf ρ ey ≠ callKey st.fs.roots pc) ∧
    ∀ t x, t ≠ k → Γc !! t = some x → callKey st.fs.roots x.1.2 = callKey st.fs.roots pc → False := by
  rcases gd with _ | ⟨t, ⟨sg, pg⟩, g⟩
  · simp only [WholeG] at hw
    refine ⟨fun ρ _ hck => hck.whole k _ hk hw, fun t x hne hx hkx => ?_⟩
    have := (hexcl t x hne hx hkx).2
    rw [hw] at this; exact absurd this (by simp)
  · simp only [WholeG] at hw
    have hg := hgd t _ rfl
    refine ⟨fun ρ _ hck => hck.pair k ((s0, pc), q) t ((sg, pg), g) hk hg hw.2.2 hw.1 hw.2.1,
      fun c x hne hx hkx => ?_⟩
    have h1 := hval c x t ((sg, pg), g) hne hx hg hkx hw.2.2
    have h2 := x.2.2
    simp only at h1
    grind

/-- A call holding its key's whole permission is the only call of its key in flight (guards
included). -/
theorem sole_of {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) {k s0 : Nat} {pc : GoString} {q : Qp}
    (hexcl : ∀ t x, t ≠ k → Γc !! t = some x → callKey st.fs.roots x.1.2 = callKey st.fs.roots pc →
      x.2.val < 1 ∧ q.val < 1)
    (hval : ∀ t g, Γg !! t = some g → callKey st.fs.roots g.1.2 = callKey st.fs.roots pc →
      q.val + g.2.val ≤ 1) :
    q = 1 → ∀ k' s', st.proc.calls !! k' = some s' →
      callKey st.fs.roots s'.2 = callKey st.fs.roots pc → k' = k := by
  intro hq k' s' hk' hks
  refine Classical.byContradiction fun hne => ?_
  rcases hc.cover k' s' hk' with h1 | h1
  · cases hx : Γc !! k' with
    | none => exact h1 hx
    | some x =>
      have hxs : x.1 = s' := by have := hc.calls k' x hx; rw [hk'] at this; cases this; rfl
      have := (hexcl k' x hne hx (by rw [hxs]; exact hks)).2
      rw [hq] at this; exact absurd this (by simp)
  · cases hx : Γg !! k' with
    | none => exact h1 hx
    | some x =>
      have hxs : x.1 = s' := by have := hc.gcalls k' x hx; rw [hk'] at this; cases this; rfl
      have h2 := hval k' x hx (by rw [hxs]; exact hks)
      have h3 := x.2.2
      rw [hq] at h2
      grind

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
    (hdirs : ∀ x, x ∈ e.op.apply V.now → x ∈ V.now ∨ x ∈ e.op.newDirs)
    (hst : e.start ≤ V.2.length) :
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · intro x e' hx
    rcases getElem?_snoc_cases hx with ⟨-, hx⟩ | ⟨rfl, rfl⟩
    · exact hcoh.starts x e' hx
    · exact hst

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

/-- **The root clause of a logging step** (`wp_logStepSWG`'s `htree`) for claims all of the
directory `j` that `d` names, the call on `d/b`. -/
theorem rootClause_one {st : OsState} {R : Roots} (hR : st.fs.roots = R) {d : GoString} {j : Ino}
    (hp : st.lookup d = some (.dir j)) (b : GoString) {cl : List ClaimW} (hcl : ∀ c ∈ cl, c.1 = j) :
    ∃ rj ∈ R, IsUnder rj.1 (child d b) ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1 := by
  obtain ⟨rj, hrj, -, hch, hre⟩ := reachFrom_of_lookup hp
  exact ⟨rj, hR ▸ hrj, hch b, fun c hc => (hcl c hc) ▸ hre⟩

/-- The root clause for claims of the directories `j` and `j'` that `d` and `d'` name, the call on
`d/bs`, the two names in one root's tree. -/
theorem rootClause_two {st : OsState} {R : Roots} (hRok : RootsOk st.fs.roots) (hR : st.fs.roots = R)
    {d d' bs bt : GoString} {j j' : Ino} (hp : st.lookup d = some (.dir j))
    (hp' : st.lookup d' = some (.dir j')) (hsr : SameRootR R (child d bs) (child d' bt))
    {cl : List ClaimW} (hcl : ∀ c ∈ cl, c.1 = j ∨ c.1 = j') :
    ∃ rj ∈ R, IsUnder rj.1 (child d bs) ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1 := by
  obtain ⟨rj, hrj, -, hch, hre⟩ := reachFrom_of_lookup hp
  obtain ⟨rj', hrj', -, hch', hre'⟩ := reachFrom_of_lookup hp'
  obtain ⟨r0, hr0, h0, h0'⟩ := hsr
  rw [← hR] at hr0
  have e1 := root_of_isUnder hRok hrj hr0 (hch bs) h0
  have e2 := root_of_isUnder hRok hrj' hr0 (hch' bt) h0'
  refine ⟨rj, hR ▸ hrj, hch bs, fun c hc => ?_⟩
  rcases hcl c hc with h | h
  · exact h ▸ hre
  · rw [h, e1, ← e2]; exact hre'

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

/-- The calls in flight other than `k` of `k`'s key, each with its fraction of the key's
permission, and `k`'s: neither is the whole permission. -/
theorem callResS_excl (R : Roots) (Γc : GMap Nat CallV) (k : Nat) (x0 : CallV)
    (hk : Γc !! k = some x0) :
    ⊢ callResS (gooseOsGS (L := L)) R Γc -∗
      ⌜∀ t x, t ≠ k → Γc !! t = some x → callKey R x.1.2 = callKey R x0.1.2 →
        x.2.val < 1 ∧ x0.2.val < 1⌝ ∗
        callResS (gooseOsGS (L := L)) R Γc := by
  iintro H
  by_cases hP : ∀ t x, t ≠ k → Γc !! t = some x → callKey R x.1.2 = callKey R x0.1.2 →
      x.2.val < 1 ∧ x0.2.val < 1
  · isplitr
    · ipureintro; exact hP
    · iexact H
  · have : ∃ t x, t ≠ k ∧ Γc !! t = some x ∧ callKey R x.1.2 = callKey R x0.1.2 ∧
        ¬ (x.2.val < 1 ∧ x0.2.val < 1) :=
      Classical.byContradiction fun hn => hP fun t x hne ht hkx =>
        Classical.byContradiction fun hv => hn ⟨t, x, hne, ht, hkx, hv⟩
    obtain ⟨t, x, hne, ht, hkx, hv⟩ := this
    unfold callResS
    icases (BigSepM.bigSepM_delete (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R x.1.2) (DFrac.own x.2) ())
      hk).1 $$ H
      with ⟨Hq, H⟩
    have ht' : (GMap.delete k Γc) !! t = some x := by
      rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact ht
    icases (BigSepM.bigSepM_lookup (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R x.1.2) (DFrac.own x.2) ())
      ht') $$ H
      with Ht
    rw [hkx]
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hq Ht with %Hv
    exact absurd ⟨DFrac.valid_op_own Hv.1, DFrac.valid_own_op Hv.1⟩ hv

/-- The fractions of the permission of the key of `pc` the logging calls `Γc` and the guard calls
`Γg` of that key hold: for the call `k` (holding `q`), another logging call's, `q` and a guard's
make at most the whole; so do `q` and a guard's. -/
theorem callsRes_facts (R : Roots) (Γc Γg : GMap Nat CallV) (k s0 : Nat) (pc : GoString) (q : Qp)
    (hk : Γc !! k = some ((s0, pc), q)) :
    ⊢ callResS (gooseOsGS (L := L)) R Γc -∗ callResS (gooseOsGS (L := L)) R Γg -∗
      ⌜(∀ c x t g, c ≠ k → Γc !! c = some x → Γg !! t = some g →
          callKey R x.1.2 = callKey R pc → callKey R g.1.2 = callKey R pc →
          x.2.val + q.val + g.2.val ≤ 1) ∧
        (∀ t g, Γg !! t = some g → callKey R g.1.2 = callKey R pc → q.val + g.2.val ≤ 1)⌝ ∗
      callResS (gooseOsGS (L := L)) R Γc ∗ callResS (gooseOsGS (L := L)) R Γg := by
  iintro Hc Hg
  by_cases hP : (∀ c x t g, c ≠ k → Γc !! c = some x → Γg !! t = some g →
          callKey R x.1.2 = callKey R pc → callKey R g.1.2 = callKey R pc →
          x.2.val + q.val + g.2.val ≤ 1) ∧
        (∀ t g, Γg !! t = some g → callKey R g.1.2 = callKey R pc → q.val + g.2.val ≤ 1)
  · isplitr [Hc Hg]
    · ipureintro; exact hP
    · iframe
  iexfalso
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : CallV) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R x.1.2) (DFrac.own x.2) ())
    hk).1 $$ Hc
    with ⟨Hq, Hc⟩
  by_cases h1 : ∀ c x t g, c ≠ k → Γc !! c = some x → Γg !! t = some g →
      callKey R x.1.2 = callKey R pc → callKey R g.1.2 = callKey R pc →
      x.2.val + q.val + g.2.val ≤ 1
  · have : ∃ t g, Γg !! t = some g ∧ callKey R g.1.2 = callKey R pc ∧ ¬ q.val + g.2.val ≤ 1 :=
      Classical.byContradiction fun hn => hP ⟨h1, fun t g ht hkg =>
        Classical.byContradiction fun hv => hn ⟨t, g, ht, hkg, hv⟩⟩
    obtain ⟨t, g, ht, hkg, hv⟩ := this
    icases (BigSepM.bigSepM_lookup (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R x.1.2) (DFrac.own x.2) ())
      ht) $$ Hg
      with Ht
    rw [hkg]
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hq Ht with %Hv
    exact absurd (DFrac.valid_own.1 Hv.1) hv
  · have : ∃ c x t g, c ≠ k ∧ Γc !! c = some x ∧ Γg !! t = some g ∧
        callKey R x.1.2 = callKey R pc ∧ callKey R g.1.2 = callKey R pc ∧
        ¬ x.2.val + q.val + g.2.val ≤ 1 :=
      Classical.byContradiction fun hn => h1 fun c x t g hne hc ht hkx hkg =>
        Classical.byContradiction fun hv => hn ⟨c, x, t, g, hne, hc, ht, hkx, hkg, hv⟩
    obtain ⟨c, x, t, g, hne, hc, ht, hkx, hkg, hv⟩ := this
    have hc' : (GMap.delete k Γc) !! c = some x := by
      rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact hc
    icases (BigSepM.bigSepM_lookup (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R x.1.2) (DFrac.own x.2) ())
      hc') $$ Hc
      with Hx
    icases (BigSepM.bigSepM_lookup (M := GMap Nat)
      (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R x.1.2) (DFrac.own x.2) ())
      ht) $$ Hg
      with Ht
    rw [hkx, hkg]
    ihave Hxq : iprop(gElem (K := GoString) (V := Unit) (gooseOsGS (L := L))
      (gooseOsGS (L := L)).γperm (callKey R pc) (DFrac.own (x.2 + q)) ()) $$ [Hx Hq]
    · iapply (gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey R pc) x.2 q ()).2
      iframe
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hxq Ht with %Hv
    exact absurd (DFrac.valid_own.1 Hv.1) hv

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

/-- A guard, or nothing: what a directory operation's call may hold beside its fraction. -/
def osGuardOpt : Option (Nat × CallV) → IProp GF
  | none => iprop(emp)
  | some (t, (sg, pg), g) => osGuardS (L := L) t sg pg g

/-- The call `k` in flight (`osCallS`), with the guard `gd` if any. -/
def osCallSG (k s0 : Nat) (pc : GoString) (q : Qp) : Option (Nat × CallV) → IProp GF
  | none => osCallS (L := L) k s0 pc q
  | some (t, (sg, pg), g) => iprop(osCallS (L := L) k s0 pc q ∗ osGuardS (L := L) t sg pg g)

/-- The call's fraction back (`osCallPerm`), with the guard `gd` if any. -/
def osCallPermG (r : GoString) (q : Qp) : Option (Nat × CallV) → IProp GF
  | none => osCallPerm (L := L) r q
  | some (t, (sg, pg), g) => iprop(osCallPerm (L := L) r q ∗ osGuardS (L := L) t sg pg g)

theorem osCallSG_split (k s0 : Nat) (pc : GoString) (q : Qp) (gd : Option (Nat × CallV)) :
    ⊢ osCallSG (L := L) k s0 pc q gd -∗ osCallS (L := L) k s0 pc q ∗ osGuardOpt (L := L) gd := by
  rcases gd with _ | ⟨t, ⟨sg, pg⟩, g⟩
  · simp only [osCallSG, osGuardOpt]
    iintro H; isplitl [H]
    · iexact H
    · iempintro
  · simp only [osCallSG, osGuardOpt]
    iintro ⟨H1, H2⟩; isplitl [H1]
    · iexact H1
    · iexact H2

theorem osCallPermG_join (r : GoString) (q : Qp) (gd : Option (Nat × CallV)) :
    ⊢ osCallPerm (L := L) r q -∗ osGuardOpt (L := L) gd -∗ osCallPermG (L := L) r q gd := by
  rcases gd with _ | ⟨t, ⟨sg, pg⟩, g⟩
  · simp only [osCallPermG, osGuardOpt]
    iintro H -; iexact H
  · simp only [osCallPermG, osGuardOpt]
    iintro H1 H2; isplitl [H1]
    · iexact H1
    · iexact H2

theorem osCallSG_none (k s0 : Nat) (pc : GoString) (q : Qp) :
    ⊢ osCallS (L := L) k s0 pc q -∗ osCallSG (L := L) k s0 pc q none := by
  simp only [osCallSG]; iintro H; iexact H

theorem osCallPermG_none (r : GoString) (q : Qp) :
    ⊢ osCallPermG (L := L) r q none -∗ osCallPerm (L := L) r q := by
  simp only [osCallPermG]; iintro H; iexact H

/-- A guard is one of the authority's. -/
theorem osGuardOpt_lookup (Γg : GMap Nat CallV) (gd : Option (Nat × CallV)) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γg Γg -∗ osGuardOpt (L := L) gd -∗
      ⌜∀ t x, gd = some (t, x) → Γg !! t = some x⌝ := by
  rcases gd with _ | ⟨t, ⟨sg, pg⟩, g⟩
  · iintro _ _
    ipureintro; intro t x h; cases h
  · iintro HA H
    unfold osGuardOpt osGuardS
    icases gAuth_lookup _ _ _ _ _ _ $$ HA H with %hl
    ipureintro; intro t' x h; cases h; exact hl

/-- `st'` is `st` after a step of the call `k` that only ended it, as the tree sees it (the files
may have changed: an fd opened). -/
structure EndedT (st st' : OsState) (k : Nat) : Prop where
  roots : st'.fs.roots = st.fs.roots
  dur : st'.fs.treeDur = st.fs.treeDur
  log : st'.fs.metaLog = st.fs.metaLog
  committed : st'.fs.committed = st.fs.committed
  dfds : st'.proc.dfds = st.proc.dfds
  calls : st'.proc.calls = GMap.delete k st.proc.calls

/-- `st'` is `st` after a step of the call `k` (begun at `s0`) that logged `o`, as the tree sees it
(the files may have changed: a file created). -/
structure LoggedT (st st' : OsState) (k s0 : Nat) (o : MetaOp) : Prop where
  roots : st'.fs.roots = st.fs.roots
  dur : st'.fs.treeDur = st.fs.treeDur
  log : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s0⟩]
  committed : st'.fs.committed = st.fs.committed
  dfds : st'.proc.dfds = GMap.fmap (·.note o) st.proc.dfds
  calls : st'.proc.calls = GMap.delete k st.proc.calls

theorem LoggedT.tree {st st' : OsState} {k s0 : Nat} {o : MetaOp} (h : LoggedT st st' k s0 o) :
    st'.tree = o.apply st.tree := by
  simp only [OsState.tree, h.dur, h.log, List.map_append, List.map_cons, List.map_nil]
  rw [replay_snoc]

theorem LoggedFrom.toT {st st' : OsState} {k s0 : Nat} {o : MetaOp} (h : LoggedFrom st st' k s0 o) :
    LoggedT st st' k s0 o := ⟨h.roots, h.dur, h.log, h.committed, h.dfds, h.calls⟩

theorem endedT_metaEnd (st : OsState) (k : Nat) : EndedT st (st.metaEnd k) k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `wp_logStepSWG` whose `hpost` also gets the semantics' own step (`fsSemWithS`'s premise on
steps, `FsStepSat`; session S3d). -/
theorem wp_logStepSWGQ (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (gd : Option (Nat × CallV)) (oF : Nat → MetaOp) (cl : List ClaimW) (curF : Nat → ClaimW → Ents) (F : IProp GF)
    (P : OsState → Prop) (W : val → Bool → Prop) (G : Nat → val → Bool → IProp GF)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ n, ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ (oF n).Writes c.1 b)
    (hslots : ∀ n, ∀ sl ∈ (oF n).slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ WholeG R pc q s0 gd)
    (hdir : ∀ n, (oF n).IsDirOp → WholeG R pc q s0 gd)
    (hadd : ∀ n j b, b ∈ (oF n).adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' →
      (∃ hh hh', ExtSemantics.step (E := fsExt) op v hh st () e' hh' st' ()) →
      ∃ w, e' = Val w ∧ FsTreeWf st' ∧
        ((EndedT st st' k ∧ W w false) ∨
         (LoggedT st st' k s0 (oF st.fs.nextIno) ∧ W w true)))
    (hworld : ∀ st e' st' h h' Γb Γm Γf Γt w lg, FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, pc) → (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) →
      P st → ClaimsAt st cl → IsFsStep op v st e' st' → e' = Val w → W w lg →
      (lg = false → EndedT st st' k) → (lg = true → LoggedT st st' k s0 (oF st.fs.nextIno)) →
      HeapRendered st st' h h' → MapsFresh st st' h →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗ ∃ Γb' Γm' Γf' Γt',
        osWorld (L := L) st' Γb' Γm' Γf' Γt' h' ∗ G st.fs.nextIno w lg)
    (htree : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → LoggedT st st' k s0 (oF st.fs.nextIno) →
      let o := oF st.fs.nextIno
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide)
    (hl : ¬ LockOp op := by simp [LockOp]) (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallSG (L := L) k s0 pc q gd -∗
      (∀ w, osCallPermG (L := L) (callKey R pc) q gd -∗ F -∗
        ((⌜W w false⌝ ∗ (∃ n, G n w false) ∗
            [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ n x, G n w true ∗ osLogged (L := L) x ⟨oF n, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF n, s0⟩ (curF n c))) ∗
           [∗list] J ∈ (oF n).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ1
  icases osCallSG_split k s0 pc q gd $$ Hk with ⟨Hk, Hgd⟩
  iapply wp_fs_stepMX op _ Φ hv hE hO hl hM $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  ihave HΦ : (∀ w, osCallPerm (L := L) (callKey R pc) q -∗ osGuardOpt (L := L) gd -∗ F -∗
        ((⌜W w false⌝ ∗ G st.fs.nextIno w false ∗
            [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ G st.fs.nextIno w true ∗ ∃ x, osLogged (L := L) x ⟨oF st.fs.nextIno, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF st.fs.nextIno, s0⟩ (curF st.fs.nextIno c))) ∗
           [∗list] J ∈ (oF st.fs.nextIno).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) $$ [HΦ1]
  · iintro %w Hq Hgd HF Hp
    iapply HΦ1 $$ %w [Hq Hgd] HF
    · iapply osCallPermG_join $$ Hq Hgd
    icases Hp with (⟨%hW, HG, Hp⟩ | ⟨%hW, HG, %x, Hp⟩)
    · ileft
      isplitr
      · ipureintro; exact hW
      isplitl [HG]
      · iexists st.fs.nextIno; iexact HG
      · iexact Hp
    · iright
      isplitr
      · ipureintro; exact hW
      · iexists st.fs.nextIno, x; isplitl [HG]
        · iexact HG
        · iexact Hp
  have hwr := hwr st.fs.nextIno
  have hslots := hslots st.fs.nextIno
  have hdir := hdir st.fs.nextIno
  have hadd := hadd st.fs.nextIno
  have hpost0 := hpost st
  have htree0 := htree st
  have hworld0 := hworld st
  clear hpost htree hworld
  generalize oF st.fs.nextIno = o at hwr hslots hdir hadd hpost0 htree0 hworld0 ⊢
  generalize curF st.fs.nextIno = cur at htree0 ⊢
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
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
  have hcall : st.proc.calls !! k = some (s0, pc) := by
    exact hc.calls k _ hk
  icases callResS_excl st.fs.roots Γc k ((s0, pc), q) hk $$ Hcr with ⟨%hexcl, Hcr⟩
  icases callsRes_facts st.fs.roots Γc Γg k s0 pc q hk $$ Hcr Hgr with ⟨%hval, Hcr, Hgr⟩
  icases osGuardOpt_lookup Γg gd $$ HAg Hgd with %hgd
  have hsole : q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc →
      k' = k := by
    rw [← hR]; exact sole_of (s0 := s0) hc hexcl hval.2
  have hwhole := fun (hwg : WholeG R pc q s0 gd) => wholeG_facts hc hk hexcl hval.1 hgd (by rw [hR]; exact hwg)
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
  obtain ⟨⟨Hst, Hfr, Hr⟩, Hsem⟩ := Hst
  obtain ⟨w, rfl, hwf', hres⟩ := hpost0 e' st' hw hR hcall hsole hP hat Hst ⟨_, _, Hsem⟩
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : CallV) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey st.fs.roots x.1.2) (DFrac.own x.2) ())
      hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  rcases hres with ⟨hend, hW⟩ | ⟨hlf, hW⟩
  · -- no effect: the call ended
    imod hworld0 _ st' h h' Γb Γm Γf Γt w false hw hR hcall hsole hP hat Hst rfl hW
      (fun _ => hend) (fun hh => by cases hh) Hr Hfr $$ Hw with ⟨%Γb', %Γm', %Γf', %Γt', Hw, HG⟩
    imod Hclose $$ [Hs HAn Halen HAlog] with -
    · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · iapply (treeCtx_eq _ _).2
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st')
          (commitGrows_of_eq hend.committed) $$ Hcm
      try unfold treeCtxT
      iexists Γdf, GMap.delete k Γc, Γg
      try unfold callResS
      rw [hend.roots, hend.dur, hend.log]
      iframe
      ipureintro
      exact ⟨hwf', (treeCohS_metaEnd hc k hk).congr hend.dur hend.log hend.dfds hend.calls hend.roots⟩
    iapply wp_value'
    iapply HΦ $$ %w [Hq] Hgd HF
    · unfold osCallPerm; rw [← hR]; iexact Hq
    ileft
    isplitr
    · ipureintro; exact hW
    isplitl [HG]
    · iexact HG
    · iexact Hcl
  · -- logged
    obtain ⟨hdirs, hnew, hok, hcur, rj, hrjR, hpcU, hreach⟩ := htree0 _ st' hw hR hcall hP hat Hst hlf
    have htr := hlf.tree
    have hrj : (rj.1, rj.2) ∈ st.fs.roots := by rw [hR]; exact hrjR
    have hkeyR : callKey st.fs.roots pc = rj.1 := callKey_eq hw.roots hrj hpcU
    -- the claims' directories are of the root of the call's path
    have hclρ : ∀ ρ, RootCoh st ρ → ∀ c ∈ cl, ρ c.1 = rj.1 := by
      intro ρ hrc c hcm
      have hre := hreach c hcm
      rw [tree_prefTree] at hre
      exact rho_of_reachFrom hrc.tags.roots (hrc.tags.ents _ (Nat.zero_le _) (Nat.le_refl _)) hrj hre
    have hρ : ∀ ρ, RootCoh st ρ → ∃ ρ' : Ino → GoString, (∀ j, j ∈ st.tree → ρ' j = ρ j) ∧
        (∀ j b, o.Writes j b → ρ' j = ρ' o.dir) ∧ (∀ j b, o.Writes j b → j ∈ o.apply st.tree) ∧
        ρ' o.dir = callKey st.fs.roots pc := by
      intro ρ hrc
      have hsl : ∀ j b, (j, b) ∈ o.slots → j ∈ st.tree ∧ ρ j = rj.1 := by
        intro j b hjb
        obtain ⟨c, hcm, hc1, -⟩ := hslots (j, b) hjb
        simp only at hc1; subst hc1
        exact ⟨hcoh.2.dirs _ _ _ (hlk c hcm).1, hclρ ρ hrc c hcm⟩
      obtain ⟨bd, hbd⟩ := dir_mem_slots o
      have hnin : ∀ j, j ∈ st.tree → j ∉ o.newDirs := fun j hj hn => hnew j hn hj
      classical
      have hd : (if o.dir ∈ o.newDirs then ρ o.dir else ρ o.dir) = ρ o.dir := by split <;> rfl
      refine ⟨fun j => if j ∈ o.newDirs then ρ o.dir else ρ j, fun j hj => if_neg (hnin j hj), ?_, ?_,
        by simp only [hd]; rw [(hsl _ _ hbd).2, hkeyR]⟩
      · intro j b hwj
        simp only [hd]
        rcases writes_cases o j b hwj with h | h
        · rw [if_neg (hnin j (hsl j b h).1), (hsl j b h).2, (hsl _ _ hbd).2]
        · rw [if_pos h]
      · intro j b hwj
        rcases writes_cases o j b hwj with h | h
        · exact mem_apply_of_mem _ _ _ (hsl j b h).1
        · exact mem_apply_newDirs o st.tree j h
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
      · obtain ⟨ρ, hrc, hck⟩ := hc.rc
        refine Nat.lt_of_not_le fun hys => (hwhole hq1).1 ρ hrc hck y ey hys hy ?_
        have hwr : ey.op.Writes c.1 sl.2 := .inl (by rw [hc1]; exact hsl')
        rw [← hrc.tags.ops y ey (by omega) hy c.1 sl.2 hwr, hclρ ρ hrc c hcm, hkeyR]
    have hcoh' : TreeCohS st' Γdf (GMap.delete k Γc) Γg :=
      treeCohS_log hc hk o hlf.dur hlf.log hlf.dfds hlf.calls htr hpss
        (fun hd ρ hrc hck => (hwhole (hdir hd)).1 ρ hrc hck)
        (fun t x hne hx hkx => ⟨(hexcl t x hne hx hkx).1, fun hd => (hwhole (hdir hd)).2 t x hne hx hkx⟩)
        (fun c x t g hne hx hg hkx hkg => hval.1 c x t g hne hx hg hkx hkg) hok hadd hw hlf.roots hρ
    have hnc := namesCoh_log hcoh.2 ⟨o, s0⟩ (cl.map (fun c => (c.1, c.2.1)))
      (fun kk hkk => by
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hkk
        exact ⟨_, (hlk c hcm).1⟩)
      (fun sl hsl => by
        obtain ⟨c, hcm, hc1, hc2⟩ := hslots sl hsl
        exact ⟨(c.1, c.2.1), List.mem_map.2 ⟨c, hcm, rfl⟩, hc1, hc2⟩)
      hnew hdirs (hc.callsLe k _ hk)
    have hcl' : ∀ c ∈ cl, c.2.2.1.log st.fs.metaLog.length ⟨o, s0⟩ (cur c) =
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
      (fun c => c.2.2.1.log st.fs.metaLog.length ⟨o, s0⟩ (cur c)) cl Γn hne hcl' $$ HAn Hcl
      with ⟨HAn, Hcl⟩
    imod hworld0 _ st' h h' Γb Γm Γf Γt w true hw hR hcall hsole hP hat Hst rfl hW
      (fun hh => by cases hh) (fun _ => hlf) Hr Hfr $$ Hw with ⟨%Γb', %Γm', %Γf', %Γt', Hw, HG⟩
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
      iexists Γb', Γm', Γf', Γt'
      isplitl [Hw]
      · unfold osWorld; iexact Hw
      isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
      · iapply (treeCtx_eq _ _).2
        isplitr [Hcm]
        rotate_left
        · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st')
            (commitGrows_of_eq hlf.committed) $$ Hcm
        unfold treeCtxT
        iexists Γdf, GMap.delete k Γc, Γg
        try unfold callResS
        rw [hlf.roots, hlf.dur, hlf.log]
        iframe
        ipureintro; exact ⟨hwf', hcoh'⟩
      iapply wp_value'
      iapply HΦ $$ %w [Hq] Hgd HF
      · unfold osCallPerm; rw [← hR]; iexact Hq
      iright
      isplitr
      · ipureintro; exact hW
      isplitl [HG]
      · iexact HG
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
      iexists Γb', Γm', Γf', Γt'
      isplitl [Hw]
      · unfold osWorld; iexact Hw
      isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
      · iapply (treeCtx_eq _ _).2
        isplitr [Hcm]
        rotate_left
        · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st')
            (commitGrows_of_eq hlf.committed) $$ Hcm
        unfold treeCtxT
        iexists Γdf, GMap.delete k Γc, Γg
        try unfold callResS
        rw [hlf.roots, hlf.dur, hlf.log]
        iframe
        ipureintro; exact ⟨hwf', hcoh'⟩
      iapply wp_value'
      iapply HΦ $$ %w [Hq] Hgd HF
      · unfold osCallPerm; rw [← hR]; iexact Hq
      iright
      isplitr
      · ipureintro; exact hW
      isplitl [HG]
      · iexact HG
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



/-- **A step that logs `o` for the call `k`** (or only ends it), the claims `cl` (whole) written:
from what it finds of the state (`P`, given by the caller's resources `F` through the claims'
authority; `ClaimsAt`: what the claims know) and what it returns (`W w logged`). The obligations:
each claim is written and every slot `o` writes is in one; the claims' `next` bound the call's
start (or the call holds the whole permission); a directory operation holds the whole permission;
the tree after a logged `o` has the old directories and the new ones (fresh), `o` is applicable if
a file operation, and the claims' entries after `o` are as given.
The operation `oF n` and the claims' new entries `curF n` are functions of the step's fresh inode
`n` (the state's `nextIno`, which the logic does not track: `mkdir`, `open(O_CREAT)`). The step
may change the files' world (`hworld`, giving `G n w logged`: `open(O_CREAT)`'s new file and fd);
it ends the call (`EndedT`) or logs (`LoggedT`), its new state well formed (`hpost`). -/
theorem wp_logStepSWG (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (gd : Option (Nat × CallV)) (oF : Nat → MetaOp) (cl : List ClaimW) (curF : Nat → ClaimW → Ents) (F : IProp GF)
    (P : OsState → Prop) (W : val → Bool → Prop) (G : Nat → val → Bool → IProp GF)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ n, ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ (oF n).Writes c.1 b)
    (hslots : ∀ n, ∀ sl ∈ (oF n).slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ WholeG R pc q s0 gd)
    (hdir : ∀ n, (oF n).IsDirOp → WholeG R pc q s0 gd)
    (hadd : ∀ n j b, b ∈ (oF n).adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧ FsTreeWf st' ∧
        ((EndedT st st' k ∧ W w false) ∨
         (LoggedT st st' k s0 (oF st.fs.nextIno) ∧ W w true)))
    (hworld : ∀ st e' st' h h' Γb Γm Γf Γt w lg, FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, pc) → (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) →
      P st → ClaimsAt st cl → IsFsStep op v st e' st' → e' = Val w → W w lg →
      (lg = false → EndedT st st' k) → (lg = true → LoggedT st st' k s0 (oF st.fs.nextIno)) →
      HeapRendered st st' h h' → MapsFresh st st' h →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗ ∃ Γb' Γm' Γf' Γt',
        osWorld (L := L) st' Γb' Γm' Γf' Γt' h' ∗ G st.fs.nextIno w lg)
    (htree : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → LoggedT st st' k s0 (oF st.fs.nextIno) →
      let o := oF st.fs.nextIno
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide)
    (hl : ¬ LockOp op := by simp [LockOp]) (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallSG (L := L) k s0 pc q gd -∗
      (∀ w, osCallPermG (L := L) (callKey R pc) q gd -∗ F -∗
        ((⌜W w false⌝ ∗ (∃ n, G n w false) ∗
            [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ n x, G n w true ∗ osLogged (L := L) x ⟨oF n, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF n, s0⟩ (curF n c))) ∗
           [∗list] J ∈ (oF n).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ1
  iapply wp_logStepSWGQ op v hv R k s0 pc q gd oF cl curF F P W G hne hwr hslots hnext hdir hadd hF
    hprog (fun st e' st' a b c d e f g _ => hpost st e' st' a b c d e f g) hworld htree hE hE' Φ
    hO hl hM $$ Hinv Hsi HF Hcl Hk HΦ1

/-- **A step that logs `o` for the call `k`** (`wp_logStepSWG` with no guard; or only ends it), the claims `cl` (whole) written:
from what it finds of the state (`P`, given by the caller's resources `F` through the claims'
authority; `ClaimsAt`: what the claims know) and what it returns (`W w logged`). The obligations:
each claim is written and every slot `o` writes is in one; the claims' `next` bound the call's
start (or the call holds the whole permission); a directory operation holds the whole permission;
the tree after a logged `o` has the old directories and the new ones (fresh), `o` is applicable if
a file operation, and the claims' entries after `o` are as given.
The operation `oF n` and the claims' new entries `curF n` are functions of the step's fresh inode
`n` (the state's `nextIno`, which the logic does not track: `mkdir`, `open(O_CREAT)`). The step
may change the files' world (`hworld`, giving `G n w logged`: `open(O_CREAT)`'s new file and fd);
it ends the call (`EndedT`) or logs (`LoggedT`), its new state well formed (`hpost`). -/
theorem wp_logStepSW (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (oF : Nat → MetaOp) (cl : List ClaimW) (curF : Nat → ClaimW → Ents) (F : IProp GF)
    (P : OsState → Prop) (W : val → Bool → Prop) (G : Nat → val → Bool → IProp GF)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ n, ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ (oF n).Writes c.1 b)
    (hslots : ∀ n, ∀ sl ∈ (oF n).slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ q = 1)
    (hdir : ∀ n, (oF n).IsDirOp → q = 1)
    (hadd : ∀ n j b, b ∈ (oF n).adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧ FsTreeWf st' ∧
        ((EndedT st st' k ∧ W w false) ∨
         (LoggedT st st' k s0 (oF st.fs.nextIno) ∧ W w true)))
    (hworld : ∀ st e' st' h h' Γb Γm Γf Γt w lg, FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, pc) → (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) →
      P st → ClaimsAt st cl → IsFsStep op v st e' st' → e' = Val w → W w lg →
      (lg = false → EndedT st st' k) → (lg = true → LoggedT st st' k s0 (oF st.fs.nextIno)) →
      HeapRendered st st' h h' → MapsFresh st st' h →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗ ∃ Γb' Γm' Γf' Γt',
        osWorld (L := L) st' Γb' Γm' Γf' Γt' h' ∗ G st.fs.nextIno w lg)
    (htree : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → LoggedT st st' k s0 (oF st.fs.nextIno) →
      let o := oF st.fs.nextIno
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallS (L := L) k s0 pc q -∗
      (∀ w, osCallPerm (L := L) (callKey R pc) q -∗ F -∗
        ((⌜W w false⌝ ∗ (∃ n, G n w false) ∗
            [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ n x, G n w true ∗ osLogged (L := L) x ⟨oF n, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF n, s0⟩ (curF n c))) ∗
           [∗list] J ∈ (oF n).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSWG op v hv R k s0 pc q none oF cl curF F P W G hne hwr hslots hnext hdir hadd hF
    hprog hpost hworld htree hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl [Hk]
  · iapply osCallSG_none $$ Hk
  iintro %w Hq
  iapply HΦ $$ %w [Hq]
  iapply osCallPermG_none $$ Hq


/-- `wp_logStepSW` whose `hpost` also gets the semantics' own step (session S3d). -/
theorem wp_logStepSWQ (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (oF : Nat → MetaOp) (cl : List ClaimW) (curF : Nat → ClaimW → Ents) (F : IProp GF)
    (P : OsState → Prop) (W : val → Bool → Prop) (G : Nat → val → Bool → IProp GF)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ n, ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ (oF n).Writes c.1 b)
    (hslots : ∀ n, ∀ sl ∈ (oF n).slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ q = 1)
    (hdir : ∀ n, (oF n).IsDirOp → q = 1)
    (hadd : ∀ n j b, b ∈ (oF n).adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' →
      (∃ hh hh', ExtSemantics.step (E := fsExt) op v hh st () e' hh' st' ()) →
      ∃ w, e' = Val w ∧ FsTreeWf st' ∧
        ((EndedT st st' k ∧ W w false) ∨
         (LoggedT st st' k s0 (oF st.fs.nextIno) ∧ W w true)))
    (hworld : ∀ st e' st' h h' Γb Γm Γf Γt w lg, FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, pc) → (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) →
      P st → ClaimsAt st cl → IsFsStep op v st e' st' → e' = Val w → W w lg →
      (lg = false → EndedT st st' k) → (lg = true → LoggedT st st' k s0 (oF st.fs.nextIno)) →
      HeapRendered st st' h h' → MapsFresh st st' h →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗ ∃ Γb' Γm' Γf' Γt',
        osWorld (L := L) st' Γb' Γm' Γf' Γt' h' ∗ G st.fs.nextIno w lg)
    (htree : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → LoggedT st st' k s0 (oF st.fs.nextIno) →
      let o := oF st.fs.nextIno
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallS (L := L) k s0 pc q -∗
      (∀ w, osCallPerm (L := L) (callKey R pc) q -∗ F -∗
        ((⌜W w false⌝ ∗ (∃ n, G n w false) ∗
            [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ n x, G n w true ∗ osLogged (L := L) x ⟨oF n, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF n, s0⟩ (curF n c))) ∗
           [∗list] J ∈ (oF n).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSWGQ op v hv R k s0 pc q none oF cl curF F P W G hne hwr hslots hnext hdir hadd hF
    hprog hpost hworld htree hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl [Hk]
  · iapply osCallSG_none $$ Hk
  iintro %w Hq
  iapply HΦ $$ %w [Hq]
  iapply osCallPermG_none $$ Hq

/-- **A step that logs `o` for the call `k`** (or only ends it), the claims `cl` (whole) written:
from what it finds of the state (`P`, given by the caller's resources `F` through the claims'
authority; `ClaimsAt`: what the claims know) and what it returns (`W w logged`). The obligations:
each claim is written and every slot `o` writes is in one; the claims' `next` bound the call's
start (or the call holds the whole permission); a directory operation holds the whole permission;
the tree after `o` is well formed, names no new file, has the old directories and the new ones
(fresh), `o` is applicable if a file operation, and the claims' entries after `o` are as given.
The operation `oF n` and the claims' new entries `curF n` are functions of the step's fresh inode
`n` (the state's `nextIno`, which the logic does not track: `mkdir`); the files' world unchanged
(`wp_logStepSW` with no gift). -/
theorem wp_logStepSN (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (oF : Nat → MetaOp) (cl : List ClaimW) (curF : Nat → ClaimW → Ents) (F : IProp GF)
    (P : OsState → Prop) (W : val → Bool → Prop)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ n, ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ (oF n).Writes c.1 b)
    (hslots : ∀ n, ∀ sl ∈ (oF n).slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ q = 1)
    (hdir : ∀ n, (oF n).IsDirOp → q = 1)
    (hadd : ∀ n j b, b ∈ (oF n).adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 (oF st.fs.nextIno) ∧
          (∀ x, x ∈ (oF st.fs.nextIno).apply st.tree → x < st'.fs.nextIno) ∧ W w true)))
    (htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      let o := oF st.fs.nextIno
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallS (L := L) k s0 pc q -∗
      (∀ w, osCallPerm (L := L) (callKey R pc) q -∗ F -∗
        ((⌜W w false⌝ ∗ [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ n x, osLogged (L := L) x ⟨oF n, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF n, s0⟩ (curF n c))) ∗
           [∗list] J ∈ (oF n).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSW op v hv R k s0 pc q oF cl curF F P W (fun _ _ _ => emp) hne hwr hslots hnext
    hdir hadd hF hprog
    (fun st e' st' hw hR hcall hsole hP hat Hst => by
      obtain ⟨w, rfl, hres⟩ := hpost st e' st' hw hR hcall hsole hP hat Hst
      rcases hres with ⟨rfl, hW⟩ | ⟨hlf, hlt, hW⟩
      · exact ⟨w, rfl, fsTreeWf_metaEnd hw k, .inl ⟨endedT_metaEnd st k, hW⟩⟩
      · obtain ⟨htw, hnm, -⟩ := htree st hw hR hP hat
        exact ⟨w, rfl, hlf.wf hw (hR ▸ htw) hnm hlt, .inr ⟨hlf.toT, hW⟩⟩)
    (fun st e' st' h h' Γb Γm Γf Γt w lg hw hR hcall hsole hP hat Hst _ _ _ _ Hr Hfr => by
      have hs : FilesSame st st' := by
        obtain ⟨w', -, hres⟩ := hpost st e' st' hw hR hcall hsole hP hat Hst
        rcases hres with ⟨rfl, -⟩ | ⟨hlf, -, -⟩
        · exact filesSame_metaEnd st k
        · exact hlf.same
      iintro Hw
      imod osWorld_filesSame hs Hr Hfr $$ Hw with Hw
      imodintro
      iexists Γb, Γm, Γf, Γt
      iframe)
    (fun st _ _ hw hR _ hP hat _ _ => by
      obtain ⟨-, -, h3⟩ := htree st hw hR hP hat
      exact h3)
    hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl Hk
  iintro %w Hq HF Hp
  iapply HΦ $$ %w Hq HF
  icases Hp with (⟨%hW, -, Hp⟩ | ⟨%hW, %n, %x, -, Hp⟩)
  · ileft; isplitr
    · ipureintro; exact hW
    · iexact Hp
  · iright
    isplitr
    · ipureintro; exact hW
    · iexists n, x; iexact Hp

/-- **A step that logs `o` for the call `k`** (`wp_logStepSN` with the operation and the claims'
new entries independent of the fresh inode). -/
theorem wp_logStepS (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
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
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧ W w true)))
    (htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallS (L := L) k s0 pc q -∗
      (∀ w, osCallPerm (L := L) (callKey R pc) q -∗ F -∗
        ((⌜W w false⌝ ∗ [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ x, osLogged (L := L) x ⟨o, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨o, s0⟩ c.2.2.2)) ∗
           [∗list] J ∈ o.newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSN op v hv R k s0 pc q (fun _ => o) cl (fun _ c => c.2.2.2) F P W hne
    (fun _ => hwr) (fun _ => hslots) hnext (fun _ => hdir) (fun _ => hadd) hF hprog hpost htree
    hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl Hk
  iintro %w Hq HF Hp
  iapply HΦ $$ %w Hq HF
  icases Hp with (Hp | ⟨%hW, %n, %x, Hp⟩)
  · ileft; iexact Hp
  · iright
    isplitr
    · ipureintro; exact hW
    · iexists x; iexact Hp

/-- **A step that logs `o` for the call `k`**, with a guard if any (`wp_logStepSN`'s general form; or only ends it), the claims `cl` (whole) written:
from what it finds of the state (`P`, given by the caller's resources `F` through the claims'
authority; `ClaimsAt`: what the claims know) and what it returns (`W w logged`). The obligations:
each claim is written and every slot `o` writes is in one; the claims' `next` bound the call's
start (or the call holds the whole permission); a directory operation holds the whole permission;
the tree after `o` is well formed, names no new file, has the old directories and the new ones
(fresh), `o` is applicable if a file operation, and the claims' entries after `o` are as given.
The operation `oF n` and the claims' new entries `curF n` are functions of the step's fresh inode
`n` (the state's `nextIno`, which the logic does not track: `mkdir`); the files' world unchanged
(`wp_logStepSW` with no gift). -/
theorem wp_logStepSNG (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (gd : Option (Nat × CallV)) (oF : Nat → MetaOp) (cl : List ClaimW) (curF : Nat → ClaimW → Ents) (F : IProp GF)
    (P : OsState → Prop) (W : val → Bool → Prop)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ n, ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ (oF n).Writes c.1 b)
    (hslots : ∀ n, ∀ sl ∈ (oF n).slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ WholeG R pc q s0 gd)
    (hdir : ∀ n, (oF n).IsDirOp → WholeG R pc q s0 gd)
    (hadd : ∀ n j b, b ∈ (oF n).adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 (oF st.fs.nextIno) ∧
          (∀ x, x ∈ (oF st.fs.nextIno).apply st.tree → x < st'.fs.nextIno) ∧ W w true)))
    (htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      let o := oF st.fs.nextIno
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallSG (L := L) k s0 pc q gd -∗
      (∀ w, osCallPermG (L := L) (callKey R pc) q gd -∗ F -∗
        ((⌜W w false⌝ ∗ [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ n x, osLogged (L := L) x ⟨oF n, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨oF n, s0⟩ (curF n c))) ∗
           [∗list] J ∈ (oF n).newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSWG op v hv R k s0 pc q gd oF cl curF F P W (fun _ _ _ => emp) hne hwr hslots hnext
    hdir hadd hF hprog
    (fun st e' st' hw hR hcall hsole hP hat Hst => by
      obtain ⟨w, rfl, hres⟩ := hpost st e' st' hw hR hcall hsole hP hat Hst
      rcases hres with ⟨rfl, hW⟩ | ⟨hlf, hlt, hW⟩
      · exact ⟨w, rfl, fsTreeWf_metaEnd hw k, .inl ⟨endedT_metaEnd st k, hW⟩⟩
      · obtain ⟨htw, hnm, -⟩ := htree st hw hR hP hat
        exact ⟨w, rfl, hlf.wf hw (hR ▸ htw) hnm hlt, .inr ⟨hlf.toT, hW⟩⟩)
    (fun st e' st' h h' Γb Γm Γf Γt w lg hw hR hcall hsole hP hat Hst _ _ _ _ Hr Hfr => by
      have hs : FilesSame st st' := by
        obtain ⟨w', -, hres⟩ := hpost st e' st' hw hR hcall hsole hP hat Hst
        rcases hres with ⟨rfl, -⟩ | ⟨hlf, -, -⟩
        · exact filesSame_metaEnd st k
        · exact hlf.same
      iintro Hw
      imod osWorld_filesSame hs Hr Hfr $$ Hw with Hw
      imodintro
      iexists Γb, Γm, Γf, Γt
      iframe)
    (fun st _ _ hw hR _ hP hat _ _ => by
      obtain ⟨-, -, h3⟩ := htree st hw hR hP hat
      exact h3)
    hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl Hk
  iintro %w Hq HF Hp
  iapply HΦ $$ %w Hq HF
  icases Hp with (⟨%hW, -, Hp⟩ | ⟨%hW, %n, %x, -, Hp⟩)
  · ileft; isplitr
    · ipureintro; exact hW
    · iexact Hp
  · iright
    isplitr
    · ipureintro; exact hW
    · iexists n, x; iexact Hp

/-- **A step that logs `o` for the call `k`**, with a guard if any (`wp_logStepSNG` with the operation and the claims'
new entries independent of the fresh inode). -/
theorem wp_logStepSG (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (gd : Option (Nat × CallV)) (o : MetaOp) (cl : List ClaimW) (F : IProp GF) (P : OsState → Prop)
    (W : val → Bool → Prop)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ o.Writes c.1 b)
    (hslots : ∀ sl ∈ o.slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ WholeG R pc q s0 gd)
    (hdir : o.IsDirOp → WholeG R pc q s0 gd)
    (hadd : ∀ j b, b ∈ o.adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧ W w true)))
    (htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallSG (L := L) k s0 pc q gd -∗
      (∀ w, osCallPermG (L := L) (callKey R pc) q gd -∗ F -∗
        ((⌜W w false⌝ ∗ [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ x, osLogged (L := L) x ⟨o, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨o, s0⟩ c.2.2.2)) ∗
           [∗list] J ∈ o.newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSNG op v hv R k s0 pc q gd (fun _ => o) cl (fun _ c => c.2.2.2) F P W hne
    (fun _ => hwr) (fun _ => hslots) hnext (fun _ => hdir) (fun _ => hadd) hF hprog hpost htree
    hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl Hk
  iintro %w Hq HF Hp
  iapply HΦ $$ %w Hq HF
  icases Hp with (Hp | ⟨%hW, %n, %x, Hp⟩)
  · ileft; iexact Hp
  · iright
    isplitr
    · ipureintro; exact hW
    · iexists x; iexact Hp

end specs

end Fs
end Perennial

end
