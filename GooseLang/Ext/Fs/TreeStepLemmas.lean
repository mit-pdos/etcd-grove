/-
The facts the tree's step proofs share (`TreeShared*.lean`): a history's tree and lookups
(`Hist.st`, `lookupH`), reachability and naming in a tree (`reach_of_lookup`, `named_of_lookup`,
`wf_tree`, `mem_of_reach`, and their updates by a removal, a rename, a mkdir), the states after a
step on the tree (`setDfd`, `delDfd`, `OsState.metaEnd`'s well-formedness, `openFd`, `createdSt`),
the postconditions of the metadata operations (`MetaPost`, `UnlinkPost`, `RmdirPost`, `MkdirPost`,
`RenameDirPost`), what a directory read returns (`rdName`, `rdEnd`, `rdErr`) and the open flags
(`flRO`, `flCreat`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.World
public import GooseLang.Ext.Fs.TreeLemmas
public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- A state with the roots `R` and the history `V`'s tree (and nothing else): the one whose paths a
spec talks about. -/
def Hist.st (R : Roots) (V : Hist) : OsState :=
  { fs := { roots := R, treeDur := V.1, metaLog := V.2, committed := fun _ => False, files := ∅,
            nextIno := 0, stamp := 0 },
    proc := ProcState.empty }

/-- What `p` names, with the roots `R`, in the history `V`'s tree now. -/
def lookupH (R : Roots) (V : Hist) (p : GoString) : Option Node := (Hist.st R V).lookup p

theorem lookupH_eq (st : OsState) (p : GoString) :
    st.lookup p = lookupH st.fs.roots (st.fs.treeDur, st.fs.metaLog) p := rfl

theorem histSt_tree (R : Roots) (V : Hist) : (Hist.st R V).tree = V.now := rfl

theorem le_sum_of_mem : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ L.sum
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem L x h; simp; omega

theorem exists_fresh2 {A B : Type} (M1 : GMap Nat A) (M2 : GMap Nat B) :
    ∃ t, M1 !! t = none ∧ M2 !! t = none := by
  let n := (M1.toList.map (·.1)).sum + (M2.toList.map (·.1)).sum + 1
  refine ⟨n, ?_, ?_⟩
  · cases h : M1 !! n with
    | none => rfl
    | some v =>
      have := le_sum_of_mem (M1.toList.map (·.1)) n
        (List.mem_map.2 ⟨(n, v), (GMap.mem_toList _ _ _).2 h, rfl⟩)
      omega
  · cases h : M2 !! n with
    | none => rfl
    | some v =>
      have := le_sum_of_mem (M2.toList.map (·.1)) n
        (List.mem_map.2 ⟨(n, v), (GMap.mem_toList _ _ _).2 h, rfl⟩)
      omega

theorem reach_of_walk {R : Roots} {m : Tree} : ∀ {cs : List GoString} {j x : Ino},
    Reach R m j → walk m (.dir j) cs = some (.dir x) → Reach R m x
  | [], j, x, hj, h => by simp [walk] at h; subst h; exact hj
  | c :: cs, j, x, hj, h => by
    simp only [walk] at h
    cases he : m.entry j c with
    | none => rw [he] at h; cases h
    | some n =>
      rw [he] at h; simp only at h
      cases n with
      | dir j' => exact reach_of_walk (.child j c j' hj he) h
      | file i => cases cs <;> simp [walk] at h

/-- A directory a path names is reachable from a root. -/
theorem reach_of_lookup {st : OsState} {p : GoString} {j : Ino}
    (h : st.lookup p = some (.dir j)) : Reach st.fs.roots st.tree j := by
  obtain ⟨r, j0, cs, hrj, -, -, hw⟩ := lookup_some h
  exact reach_of_walk (.root r j0 hrj) hw

/-- A file a path names is named in the tree. -/
theorem named_of_walk {m : Tree} : ∀ {cs : List GoString} {j i : Ino},
    walk m (.dir j) cs = some (.file i) → Named m i
  | [], _, _, h => by simp [walk] at h
  | c :: cs, j, i, h => by
    simp only [walk] at h
    cases he : m.entry j c with
    | none => rw [he] at h; cases h
    | some n =>
      rw [he] at h; simp only at h
      cases n with
      | dir j' => exact named_of_walk h
      | file i' => cases cs with
        | nil => simp [walk] at h; subst h; exact ⟨j, c, he⟩
        | cons _ _ => simp [walk] at h

theorem named_of_lookup {st : OsState} {p : GoString} {i : Ino}
    (h : st.lookup p = some (.file i)) : Named st.tree i := by
  obtain ⟨r, j0, cs, -, -, -, hw⟩ := lookup_some h
  exact named_of_walk hw

theorem apply_mem_mono (o : MetaOp) (m : Tree) (x : Ino) (h : x ∈ m) : x ∈ o.apply m := by
  cases o with
  | create j b i => simp only [MetaOp.apply]; rw [mem_upd]; exact .inr h
  | mkdir j b j' =>
    simp only [MetaOp.apply]; rw [GMap.mem_iff]
    by_cases hx : j' = x
    · subst hx; simp
    · rw [GMap.lookup_insert_ne _ _ hx, ← GMap.mem_iff, mem_upd]; exact .inr h
  | remove j b n => simp only [MetaOp.apply]; rw [mem_upd]; exact .inr h
  | rename j b j' b' n old =>
    simp only [MetaOp.apply]
    split
    · rw [mem_upd, mem_upd]; exact .inr (.inr h)
    · exact h

/-- **A logged operation keeps the tree well formed**, given what it makes of the tree now. -/
theorem fsTreeWf_meta {st st' : OsState} (hw : FsTreeWf st) {o : MetaOp} {s : Nat}
    (hroots : st'.fs.roots = st.fs.roots) (hdur : st'.fs.treeDur = st.fs.treeDur)
    (hlog : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s⟩])
    (hfiles : ∀ i f, st.fs.files !! i = some f → ∃ f', st'.fs.files !! i = some f')
    (hnext : st.fs.nextIno ≤ st'.fs.nextIno)
    (htw : TreeWf st.fs.roots (o.apply st.tree))
    (hnamed : ∀ i, Named (o.apply st.tree) i → ∃ f, st'.fs.files !! i = some f)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st'.fs.nextIno)
    (hdfds : ∀ fd df, st'.proc.dfds !! fd = some df → df.ino ∈ st.tree)
    (hdisj : ∀ fd, st'.proc.fds !! fd ≠ none → st'.proc.dfds !! fd = none)
    (hflt : ∀ i, i ∈ st'.fs.files → i < st'.fs.nextIno) : FsTreeWf st' := by
  have htree : st'.tree = o.apply st.tree := by
    simp only [OsState.tree, hlog, hdur, List.map_append, List.map_cons, List.map_nil]
    rw [replay_snoc]
  refine ⟨hroots ▸ hw.roots, fun n hn => ?_, fun fd df h => ?_, hdisj, hflt⟩
  · rw [hlog] at hn ⊢; rw [hdur, hroots]
    by_cases hle : n ≤ st.fs.metaLog.length
    · rw [List.take_append_of_le_length hle]
      obtain ⟨h1, h2, h3⟩ := hw.hist n hle
      refine ⟨h1, fun i hi => ?_, fun j hj => Nat.lt_of_lt_of_le (h3 j hj) hnext⟩
      obtain ⟨f, hf⟩ := h2 i hi; exact hfiles i f hf
    · have hn' : n = st.fs.metaLog.length + 1 := by simp at hn; omega
      subst hn'
      rw [List.take_of_length_le (by simp)]
      have : replay ((st.fs.metaLog ++ [(⟨o, s⟩ : LogEntry)]).map (·.op)) st.fs.treeDur =
          o.apply st.tree := by
        simp only [List.map_append, List.map_cons, List.map_nil]; rw [replay_snoc]; rfl
      rw [this]
      exact ⟨htw, hnamed, hlt⟩
  · rw [htree]; exact apply_mem_mono o st.tree _ (hdfds fd df h)

/-- The state with the directory fd `fd` set to `df'`. -/
abbrev setDfd (st : OsState) (fd : w64) (df' : OsDirFd) : OsState :=
  st.setProc { st.proc with dfds := <[fd := df']> st.proc.dfds }

theorem filesSame_setDfd (st : OsState) (fd : w64) (df' : OsDirFd) :
    FilesSame st (setDfd st fd df') := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A directory fd set (added, or its read moved on), on a directory of the tree, at a number no
file fd has: the tree's well-formedness kept. -/
theorem fsTreeWf_setDfd {st : OsState} (hw : FsTreeWf st) {fd : w64} {df' : OsDirFd}
    (hfd : st.proc.fds !! fd = none) (hin : df'.ino ∈ st.tree) :
    FsTreeWf (setDfd st fd df') := by
  refine ⟨hw.roots, hw.hist, fun fd' df'' h' => ?_, fun fd' h' => ?_, hw.files_lt⟩
  · have h'' : (<[fd := df']> st.proc.dfds) !! fd' = some df'' := h'
    rw [GMap.lookup_insert_eq_iff] at h''
    split at h''
    · cases h''; exact hin
    · exact hw.dfds fd' df'' h''
  · show (<[fd := df']> st.proc.dfds) !! fd' = none
    rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; exact absurd hfd h'
    · exact hw.disj fd' h'

/-- The state with the directory fd `fd` gone. -/
abbrev delDfd (st : OsState) (fd : w64) : OsState :=
  st.setProc { st.proc with dfds := GMap.delete fd st.proc.dfds }

theorem fsTreeWf_delDfd {st : OsState} (hw : FsTreeWf st) (fd : w64) : FsTreeWf (delDfd st fd) := by
  refine ⟨hw.roots, hw.hist, fun fd' df' h' => ?_, fun fd' h' => ?_, hw.files_lt⟩
  · have h'' : (GMap.delete fd st.proc.dfds) !! fd' = some df' := h'
    rw [GMap.lookup_delete_iff] at h''; split at h''
    · cases h''
    · exact hw.dfds fd' df' h''
  · show (GMap.delete fd st.proc.dfds) !! fd' = none
    rw [GMap.lookup_delete_iff]; split
    · rfl
    · exact hw.disj fd' h'

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The values of a step of `Readdirnames`: a name, the end, an errno. -/
abbrev rdName (b : GoString) : val := PairV (#b) (PairV (#(0 : w64)) (#(0 : w64)))

abbrev rdEnd : val := PairV (#([] : GoString)) (PairV (#(1 : w64)) (#(0 : w64)))

abbrev rdErr (e : w64) : val := PairV (#([] : GoString)) (PairV (#(0 : w64)) (#e))

end specs

/-- A state a metadata step of the call `k` (begun at `s'`) runs in, with the roots `R` and the
history `V`, the caller holding all of it: no directory fd, no other call. -/
structure MetaPre (st : OsState) (R : Roots) (V : Hist) (k s' : Nat) (p : GoString) : Prop where
  wf : FsTreeWf st
  roots : st.fs.roots = R
  hist : V = (st.fs.treeDur, st.fs.metaLog)
  calls : st.proc.calls = {[k := (s', p)]}
  start : s' = st.fs.metaLog.length
  dfds : st.proc.dfds = ∅
  seq : Sequential st.fs.metaLog

/-- What a metadata step leaves: the files' part unchanged, the tree well formed, no call, no
directory fd, the log sequential. -/
structure MetaPost (st st' : OsState) : Prop where
  same : FilesSame st st'
  wf : FsTreeWf st'
  roots : st'.fs.roots = st.fs.roots
  calls : st'.proc.calls = ∅
  dfds : st'.proc.dfds = ∅
  seq : Sequential st'.fs.metaLog

theorem delete_singleton_self {V : Type} (k : Nat) (v : V) : GMap.delete k ({[k := v]} : GMap Nat V) = ∅ := by
  apply GMap.ext; intro t
  by_cases h : k = t
  · subst h; simp
  · simp [h]

theorem fmap_empty {A B : Type} (f : A → B) : GMap.fmap f (∅ : GMap w64 A) = ∅ := by
  apply GMap.ext; intro t; simp

theorem tree_full (st : OsState) :
    replay ((st.fs.metaLog.take st.fs.metaLog.length).map (·.op)) st.fs.treeDur = st.tree := by
  rw [List.take_length]; rfl

theorem wf_tree {st : OsState} (hw : FsTreeWf st) : TreeWf st.fs.roots st.tree ∧
    (∀ i, Named st.tree i → ∃ f, st.fs.files !! i = some f) ∧
    (∀ j, j ∈ st.tree → j < st.fs.nextIno) := by
  have := hw.hist _ (Nat.le_refl _); rwa [tree_full] at this

theorem mem_of_reach {R : Roots} {m : Tree} (hw : TreeWf R m) {j : Ino} (h : Reach R m j) : j ∈ m :=
  hw.1 j h

/-- After a metadata step that changed nothing: the call ended. -/
theorem metaPost_end {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} {pc : GoString} (hp : MetaPre st R V k s' pc) :
    MetaPost st (st.metaEnd k) ∧ ((st.metaEnd k).fs.treeDur, (st.metaEnd k).fs.metaLog) = V := by
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨hp.wf.roots, hp.wf.hist, hp.wf.dfds, hp.wf.disj, hp.wf.files_lt⟩,
    rfl, ?_, hp.dfds, hp.seq⟩, hp.hist.symm⟩
  show GMap.delete k st.proc.calls = ∅
  rw [hp.calls, delete_singleton_self]

/-- After a metadata step that logged `o`, from a state `st1` that is `st` with the call ended (and
maybe the inode counter moved), given what `o` makes of the tree. -/
theorem metaPost_do {st st1 : OsState} {R : Roots} {V : Hist} {k s' : Nat} {pc : GoString} (hp : MetaPre st R V k s' pc)
    (o : MetaOp) (hf : st1.fs.files = st.fs.files) (hfd : st1.proc.fds = st.proc.fds)
    (hin : st1.proc.inflight = st.proc.inflight) (hm : st1.proc.maps = st.proc.maps)
    (hro : st1.fs.roots = st.fs.roots) (hdu : st1.fs.treeDur = st.fs.treeDur)
    (hlo : st1.fs.metaLog = st.fs.metaLog) (hca : st1.proc.calls = ∅) (hdf : st1.proc.dfds = ∅)
    (hni : st.fs.nextIno ≤ st1.fs.nextIno)
    (htw : TreeWf st.fs.roots (o.apply st.tree)) (hnm : ∀ i, Named (o.apply st.tree) i → Named st.tree i)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st1.fs.nextIno)
    (hst : st1.fs.stamp = st.fs.stamp := by rfl) :
    MetaPost st (st1.metaDo o s') ∧
      ((st1.metaDo o s').fs.treeDur, (st1.metaDo o s').fs.metaLog) = V.push ⟨o, V.2.length⟩ := by
  obtain ⟨-, hnamed, -⟩ := wf_tree hp.wf
  have hdfds' : (st1.metaDo o s').proc.dfds = ∅ := by
    simp only [OsState.metaDo, hdf, fmap_empty]
  refine ⟨⟨⟨by simp [OsState.metaDo, hf], by simp [OsState.metaDo, hfd], by simp [OsState.metaDo, hin],
    by simp [OsState.metaDo, hm], by simp [OsState.metaDo, hst]⟩, ?_, by simp [OsState.metaDo, hro],
    by simp [OsState.metaDo, hca],
    hdfds', ?_⟩, ?_⟩
  · refine fsTreeWf_meta hp.wf (o := o) (s := s') (by simp [OsState.metaDo, hro])
      (by simp [OsState.metaDo, hdu]) (by simp [OsState.metaDo, hlo])
      (fun i f h => ⟨f, by simp [OsState.metaDo, hf, h]⟩) (by simp [OsState.metaDo]; exact hni)
      htw (fun i hi => by
        obtain ⟨f, hf'⟩ := hnamed i (hnm i hi)
        exact ⟨f, by simp [OsState.metaDo, hf, hf']⟩)
      (fun j hj => by simp [OsState.metaDo]; exact hlt j hj)
      (fun fd df h => by rw [hdfds'] at h; simp at h)
      (fun fd _ => by rw [hdfds']; simp)
      (fun i hi => by
        simp only [OsState.metaDo, hf] at hi ⊢
        exact Nat.lt_of_lt_of_le (hp.wf.files_lt i hi) hni)
  · simp only [OsState.metaDo, hlo]
    rw [hp.start]; exact sequential_snoc hp.seq
  · simp only [OsState.metaDo, hdu, hlo, Hist.push]
    rw [hp.hist, hp.start]

/-- A removal names no new file. -/
theorem named_remove (m : Tree) (j : Ino) (b : GoString) (n : Node) (i : Ino) :
    Named ((MetaOp.remove j b n).apply m) i → Named m i := by
  rintro ⟨x, c, h⟩
  simp only [MetaOp.apply] at h
  rw [entry_upd] at h
  split at h
  · by_cases hb : b = c
    · subst hb; simp at h
    · rw [GMap.lookup_delete_ne _ hb, getD_lookup] at h
      exact ⟨j, c, h⟩
  · exact ⟨x, c, h⟩

/-- A new directory names no new file. -/
theorem named_mkdir (m : Tree) (j : Ino) (b : GoString) (J : Ino) (i : Ino) :
    Named ((MetaOp.mkdir j b J).apply m) i → Named m i := by
  rintro ⟨x, c, h⟩
  simp only [MetaOp.apply, Tree.entry] at h
  by_cases hx : J = x
  · subst hx; simp at h
  · rw [GMap.lookup_insert_ne _ _ hx] at h
    have h' : (m.upd j (fun d => <[b := Node.dir J]> d)).entry x c = some (.file i) := h
    rw [entry_upd] at h'
    split at h'
    · by_cases hb : b = c
      · subst hb; simp at h'
      · rw [GMap.lookup_insert_ne _ _ hb, getD_lookup] at h'
        exact ⟨j, c, h'⟩
    · exact ⟨x, c, h'⟩

/-- A rename names no new file (it moves an entry). -/
theorem named_rename (m : Tree) (j : Ino) (b : GoString) (j' : Ino) (b' : GoString) (n : Node)
    (old : Option Node) (i : Ino) :
    Named ((MetaOp.rename j b j' b' n old).apply m) i → Named m i := by
  rintro ⟨x, c, h⟩
  simp only [MetaOp.apply] at h
  split at h
  · rename_i n0 hn0
    rw [entry_upd] at h
    split at h
    · rename_i hjx
      by_cases hb : b' = c
      · subst hb; simp at h; subst h; exact ⟨j, b, hn0⟩
      · rw [GMap.lookup_insert_ne _ _ hb, getD_lookup] at h
        exact named_remove m j b n i ⟨j', c, h⟩
    · exact named_remove m j b n i ⟨x, c, by simpa [MetaOp.apply] using h⟩
  · exact ⟨x, c, h⟩

/-- The directories after a removal or a rename: those before, and the directories it changes. -/
theorem mem_remove (m : Tree) (j : Ino) (b : GoString) (n : Node) (x : Ino)
    (h : x ∈ (MetaOp.remove j b n).apply m) : x = j ∨ x ∈ m := by
  simp only [MetaOp.apply] at h; rw [mem_upd] at h
  rcases h with h | h
  · exact .inl h.symm
  · exact .inr h

theorem mem_rename (m : Tree) (j : Ino) (b : GoString) (j' : Ino) (b' : GoString) (n : Node)
    (old : Option Node) (x : Ino) (h : x ∈ (MetaOp.rename j b j' b' n old).apply m) :
    x = j ∨ x = j' ∨ x ∈ m := by
  simp only [MetaOp.apply] at h
  split at h
  · rw [mem_upd, mem_upd] at h
    rcases h with h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h.symm
    · exact .inr (.inr h)
  · exact .inr (.inr h)

theorem mem_mkdir (m : Tree) (j : Ino) (b : GoString) (J : Ino) (x : Ino)
    (h : x ∈ (MetaOp.mkdir j b J).apply m) : x = J ∨ x = j ∨ x ∈ m := by
  simp only [MetaOp.apply] at h
  rw [GMap.mem_iff] at h
  by_cases hx : J = x
  · exact .inl hx.symm
  · rw [GMap.lookup_insert_ne _ _ hx, ← GMap.mem_iff, mem_upd] at h
    rcases h with h | h
    · exact .inr (.inl h.symm)
    · exact .inr (.inr h)

/-- The state's lookups, as a spec states them. -/
theorem lookup_pre {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} {pc : GoString} (hp : MetaPre st R V k s' pc)
    (p : GoString) : st.lookup p = lookupH R V p := by
  rw [lookupH_eq st p, hp.roots, ← hp.hist]

/-- `metaPost_do` from the state with the call ended. -/
theorem metaPost_doEnd {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} {pc : GoString} (hp : MetaPre st R V k s' pc)
    (o : MetaOp) (htw : TreeWf st.fs.roots (o.apply st.tree))
    (hnm : ∀ i, Named (o.apply st.tree) i → Named st.tree i)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st.fs.nextIno) :
    MetaPost st ((st.metaEnd k).metaDo o s') ∧
      (((st.metaEnd k).metaDo o s').fs.treeDur, ((st.metaEnd k).metaDo o s').fs.metaLog) =
        V.push ⟨o, V.2.length⟩ :=
  metaPost_do hp o rfl rfl rfl rfl rfl rfl rfl
    (by show GMap.delete k st.proc.calls = ∅; rw [hp.calls, delete_singleton_self]) hp.dfds
    (Nat.le_refl _) htw hnm hlt

/-- The token and the path of a step's value. -/
theorem tokPath_inj [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {k k' : Nat} {p p' : GoString}
    (h : PairV (osTokV k') (#p') = PairV (osTokV k) (#p)) : k' = k ∧ p' = p := by
  injection h with h1 h2
  refine ⟨?_, go.intoVal_inj h2⟩
  injection h1 with h1; exact extVal_inj h1

theorem start_eq {st : OsState} {R : Roots} {V : Hist} {k s' start : Nat}
    {pc p' : GoString} (hp : MetaPre st R V k s' pc) (h : st.proc.calls !! k = some (start, p')) :
    start = s' ∧ p' = pc := by
  rw [hp.calls] at h; simp at h; exact ⟨h.1.symm, h.2.symm⟩

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What `unlink` of `d/b` leaves (`d` the directory `j`): a file removed (on a failure, removed or
not); or a failure, unchanged. -/
def UnlinkPost (R : Roots) (V : Hist) (d b : GoString) (j : Ino) (e : w64) (V' : Hist) : Prop :=
  (∃ i, lookupH R V (child d b) = some (.file i) ∧
    ((e = 0 ∧ V' = V.push ⟨.remove j b (.file i), V.2.length⟩) ∨
     (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨.remove j b (.file i), V.2.length⟩)))) ∨
  (e ≠ 0 ∧ V' = V)

/-- What `rmdir` of `d/b` leaves (`d` the directory `j`): an empty directory removed (on a failure,
removed or not); or a failure, unchanged. -/
def RmdirPost (R : Roots) (V : Hist) (d b : GoString) (j : Ino) (e : w64) (V' : Hist) : Prop :=
  (∃ J, lookupH R V (child d b) = some (.dir J) ∧ (∀ c, V.now.entry J c = none) ∧
    ((e = 0 ∧ V' = V.push ⟨.remove j b (.dir J), V.2.length⟩) ∨
     (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨.remove j b (.dir J), V.2.length⟩)))) ∨
  (e ≠ 0 ∧ V' = V)

/-- What `mkdir` of `d/b` leaves (`d` the directory `j`): where nothing was, a new, empty directory
of an inode no directory of the tree or root has (on a failure, made or not); or a failure,
unchanged. -/
def MkdirPost (R : Roots) (V : Hist) (d b : GoString) (j : Ino) (e : w64) (V' : Hist) : Prop :=
  (lookupH R V (child d b) = none ∧ ∃ J, J ∉ V.now ∧ (∀ r, (r, J) ∉ R) ∧
    ((e = 0 ∧ V' = V.push ⟨.mkdir j b J, V.2.length⟩) ∨
     (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨.mkdir j b J, V.2.length⟩)))) ∨
  (e ≠ 0 ∧ V' = V)

/-- What a rename of `d/bs` (`d` the directory `j`) to `d'/bt` (`d'` the directory `j'`) logs, the
source naming `n`. -/
def renameOp (R : Roots) (V : Hist) (j : Ino) (bs : GoString) (j' : Ino) (d' bt : GoString)
    (n : Node) : MetaOp :=
  .rename j bs j' bt n (lookupH R V (child d' bt))

theorem tokPair_inj [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {k k' : Nat}
    {a a' b b' : GoString}
    (h : PairV (osTokV k') (PairV (#a') (#b')) = PairV (osTokV k) (PairV (#a) (#b))) :
    k' = k ∧ a' = a ∧ b' = b := by
  injection h with h1 h2
  injection h2 with h3 h4
  refine ⟨?_, go.intoVal_inj h3, go.intoVal_inj h4⟩
  injection h1 with h1; exact extVal_inj h1

theorem not_isUnder_child_self (d b : GoString) : ¬ IsUnder (child d b) d := by
  intro h
  rcases h with h | h
  · have := congrArg List.length h; simp at this
  · have := h.length_le; simp at this; omega

theorem child_inj {d b b' : GoString} (h : child d b = child d b') : b = b' := by
  have := List.append_cancel_left h; simpa using this

/-- The rename's step from what the spec knows of the source's and target's directories. -/
theorem renameOp_eq {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} {pc : GoString} (hp : MetaPre st R V k s' pc)
    {d bs d' bt : GoString} {j j' : Ino} (hbs : NameOk bs) (hbt : NameOk bt)
    (hd : st.lookup d = some (.dir j)) (hd' : st.lookup d' = some (.dir j')) {n : Node}
    (hs : st.lookup (child d bs) = some n) {o : MetaOp}
    (ho : RenameOp st (child d bs) (child d' bt) o) : o = renameOp R V j bs j' d' bt n := by
  obtain ⟨js, bs', jt, bt', n', h1, h2, h3, rfl⟩ := ho
  rw [parent_child hd hbs] at h1; rw [parent_child hd' hbt] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
  rw [hs] at h3; cases h3
  simp only [renameOp, ← lookup_pre hp]

/-- What a directory's rename leaves: the operation logged (on a failure, logged or not). -/
def RenameDirPost (V : Hist) (o : MetaOp) (e : w64) (V' : Hist) : Prop :=
  (e = 0 ∧ V' = V.push ⟨o, V.2.length⟩) ∨ (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨o, V.2.length⟩))

end specs

/-- `O_RDONLY | O_CLOEXEC`, as `os.OpenFile`'s model passes `O_RDONLY`. -/
abbrev flRO : w64 := W64 0x80000

/-- `O_RDWR | O_CREAT | O_CLOEXEC`. -/
abbrev flCreat : w64 := W64 0x80042

theorem flRO_ok : OpenFlagsOk flRO.toNat := by
  simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide

theorem flCreat_ok : OpenFlagsOk flCreat.toNat := by
  simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide

/-- The fd an open with the flags `fl` gives on the file `i`. -/
def openFd (i : Ino) (fl : w64) : OsFd :=
  ⟨i, decide (fl.toNat % 4 ≠ O_WRONLY), decide (fl.toNat % 4 ≠ O_RDONLY), none, none⟩

theorem fsTreeWf_metaEnd {st : OsState} (hw : FsTreeWf st) (k : Nat) : FsTreeWf (st.metaEnd k) :=
  ⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩

theorem filesSame_metaEnd (st : OsState) (k : Nat) : FilesSame st (st.metaEnd k) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The whole tree is well formed now. -/
theorem treeWf_now {st : OsState} (hw : FsTreeWf st) : TreeWf st.fs.roots st.tree := by
  have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).1
  rw [List.take_length] at this; exact this

/-- A directory a path names is one of the tree's. -/
theorem mem_of_lookup_dir {st : OsState} (hw : FsTreeWf st) {p : GoString} {j : Ino}
    (h : st.lookup p = some (.dir j)) : j ∈ st.tree :=
  (treeWf_now hw).1 j (reach_of_lookup h)

/-- The ghost `OsMeta` of a file just created: empty, durable, zeros from offset 0 on. -/
abbrev newMeta : OsMeta := initMeta newFile

section create
variable {st : OsState} {n : Ino}

theorem sizes_create (hn : st.file n = none) : ∀ q, (st.setFile n newFile).size q = st.size q := by
  intro q; rw [size_setFile]; split
  · subst_vars; simp [OsState.size, hn, newFile, OsFile.ofBytes, OsFile.ofDisk]
  · rfl

theorem osWf_create (hwf : OsWf st) (hn : st.file n = none) : OsWf (st.setFile n newFile) := by
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, (st.setFile n newFile).file q = some f1 := by
    intro q f0 h0; rw [file_setFile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t c h => ?_, hwf.infl_one, ?_, ?_⟩
  · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
  · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
  · obtain ⟨f0, h0⟩ := hwf.infl t c h; exact hex _ _ h0
  · intro q f1 h1
    rw [file_setFile] at h1; split at h1
    · cases h1; simp [newFile, OsFile.ofBytes, OsFile.ofDisk]
    · exact hwf.sizes q f1 h1
  · intro q f1 b p h1 hp
    rw [file_setFile] at h1; split at h1
    · cases h1; simp only [newFile, OsFile.ofBytes, OsFile.ofDisk, List.mem_singleton] at hp
      subst hp; simp
    · exact hwf.stamps q f1 b p h1 hp

theorem cellView_create (hwf : OsWf st) (hn : st.file n = none) :
    cellView (st.setFile n newFile) = cellView st := by
  have hI : ∀ q i, InflightAt (st.setFile n newFile) q i = InflightAt st q i :=
    inflightAt_congr rfl
  refine cellView_congr' hwf (osWf_create hwf hn) rfl (fun q i => ?_) hI
  by_cases hpq : n = q
  · subst hpq; unfold cellByte; rw [file_setFile_eq, hn]
    simp [newFile, OsFile.ofBytes, OsFile.ofDisk, OsFile.contents]
  · unfold cellByte; rw [file_setFile_ne _ _ hpq, hI]

theorem osCoh_create {Γb Γm Γf Γt} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hn : st.file n = none) :
    OsCoh (st.setFile n newFile) Γb (<[n := newMeta]> Γm) Γf Γt := by
  have hnt : ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ n := by
    intro t c ht hcp
    obtain ⟨f, hf⟩ := hwf.infl t c ht
    rw [hcp, hn] at hf; cases hf
  have hnt' : ∀ t ti, Γt !! t = some ti → ti.ino ≠ n := by
    intro t ti h hp
    have := hcoh.tok_file t ti h
    obtain ⟨f, hf, -⟩ := this
    rw [hp, hn] at hf; cases hf
  refine ⟨fun q => ?_, fun q m hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, hcoh.toks, hcoh.tok_is, fun t ti h => ?_, fun t ti h => ?_, fun t ti h => ?_,
    fun t ti h hk => ?_, fun q m c hm hc => ?_⟩
  · rw [files_setFile, GMap.lookup_insert_eq_iff]; split
    · simp
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm
      refine ⟨newFile, by rw [files_setFile, if_pos rfl], ?_⟩
      have := metaOk_ofDisk (st := st.setFile q newFile) (i := q) (fun _ => 0) 0
        (fun b m h => by
          intro hp
          obtain ⟨⟨f0, hf0⟩, -⟩ := hwf.maps b m h
          rw [hp] at hf0; rw [hn] at hf0; cases hf0)
        (fun t c ht hc => hnt t c ht hc)
      exact this
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m hm
      exact ⟨f1, by rw [files_setFile, if_neg hpq]; exact h1, MetaOk.transfer (st := st) (st' := st.setFile n newFile) rfl rfl hm1⟩
  · obtain ⟨f1, h1, hb, hx1⟩ := hcoh.bytes q i x hx
    have hpq : n ≠ q := fun e => by subst e; rw [hn] at h1; cases h1
    refine ⟨f1, by rw [file_setFile_ne _ _ hpq]; exact h1, hb, ?_⟩
    rw [cutOf_insert, if_neg hpq]; exact hx1
  · rw [file_setFile] at h1; split at h1
    · cases h1; simp [newFile, OsFile.ofBytes, OsFile.ofDisk] at hi
    · exact hcoh.bytes_full q f1 i h1 hi
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm (hnt' t ti h))]; exact hcoh.tok_meta t ti h
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_file t ti h
    exact ⟨f1, by rw [file_setFile_ne _ _ (Ne.symm (hnt' t ti h))]; exact h1, hrest⟩
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_cand t ti h
    exact ⟨f1, by rw [file_setFile_ne _ _ (Ne.symm (hnt' t ti h))]; exact h1, hrest⟩
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_rz t ti h hk
    exact ⟨f1, by rw [file_setFile_ne _ _ (Ne.symm (hnt' t ti h))]; exact h1, hrest⟩
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · cases hm; simp [newMeta, initMeta] at hc
    · exact hcoh.cut_le q m c hm hc

end create

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The files' world after a step that adds the fd `fd` on an existing file and otherwise leaves
the files alone (`st0`, then `fd` added). -/
theorem osWorld_addFd {st st0 : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    (hs : FilesSame st st0) {fd : w64} {d : OsFd} (hfd : st.proc.fds !! fd = none)
    (hfd0 : 0 ≤ fd.toInt) (hfile : ∃ f, st.file d.ino = some f)
    (hr : HeapRendered st (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) h h')
    (hfr : MapsFresh st (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) h) :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗
      osWorld (L := L) (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) Γb Γm
        (<[fd := d]> Γf) Γt h' ∗ osFd (L := L) fd (DFrac.own 1) d := by
  unfold osWorld
  iintro ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  have hwf0 := osWf_filesSame hs hwf
  have hcoh0 := osCoh_filesSame hs hcoh
  have hf0 : ∀ i, st0.file i = st.file i := filesSame_file hs
  have hwf' : OsWf (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) := by
    refine osWf_fds hwf0 _ (fun fd' d' h' => ?_)
    rw [GMap.lookup_insert_eq_iff] at h'; split at h'
    · cases h'; rw [hf0]; exact hfile
    · exact hwf0.fds fd' d' h'
  have hΓf : Γf = st0.proc.fds := by rw [hcoh.fds, hs.2.1]
  have hcoh' : OsCoh (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) Γb Γm
      (<[fd := d]> Γf) Γt := by
    rw [hΓf]; exact osCoh_fds hcoh0 _
  have hΓfn : Γf !! fd = none := by rw [hcoh.fds]; exact hfd
  imod gFdElem_insert _ _ _ fd d hfd0 hΓfn $$ HAf with ⟨HAf, Hfd⟩
  have hcv : cellView (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) =
      cellView st := cellView_congr hwf hwf' hs.2.2.2.1 (fun i => congrArg _ (hf0 i)) hs.2.2.1
  imod cells_same hwf hwf' hr hfr hs.2.2.2.1 hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  unfold osFd
  iframe
  ipureintro; exact ⟨hwf', hcoh'⟩

/-- The state after `open(2)` with `O_CREAT` created `b` in the directory `j` (before its fd): the
call ended, the file of the fresh inode `nextIno` made, its `create` logged. -/
abbrev createdSt (st : OsState) (k : Nat) (j : Ino) (b : GoString) (s0 : Nat) : OsState :=
  (((st.metaEnd k).setFile (st.metaEnd k).fs.nextIno newFile).takeIno).metaDo
    (.create j b (st.metaEnd k).fs.nextIno) s0

theorem filesSame_created (st : OsState) (k : Nat) (j : Ino) (b : GoString) (s0 : Nat) :
    FilesSame ((st.metaEnd k).setFile st.fs.nextIno newFile) (createdSt st k j b s0) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end specs

end Fs
end Perennial

end
