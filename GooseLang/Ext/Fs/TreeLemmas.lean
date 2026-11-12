/-
Lemmas about the directory tree (`Tree.lean`, `Impl.lean`): path resolution (`OsState.lookup`,
`OsState.parent`) of a name in a directory, and what the metadata operations keep of a well-formed
tree (`TreeWf`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Lookup
public import GooseLang.Ext.Fs.Crash
public import GooseLang.Ext.Fs.TreeGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## Paths -/

/-- The entry `b` of the directory `d`. -/
abbrev child (d b : GoString) : GoString := d ++ slashB :: b

theorem joinPath_snoc (r : GoString) (cs : List GoString) (b : GoString) :
    joinPath r (cs ++ [b]) = child (joinPath r cs) b := by
  simp [joinPath, child]

theorem joinPath_append (r : GoString) (a c : List GoString) :
    joinPath r (a ++ c) = joinPath (joinPath r a) c := by
  simp [joinPath]

theorem baseOf_child (d b : GoString) (hb : slashB ∉ b) : baseOf (d ++ slashB :: b) = b := by
  unfold baseOf
  have h1 : (d ++ slashB :: b).reverse = b.reverse ++ slashB :: d.reverse := by simp
  rw [h1]
  have h2 : ∀ x ∈ b.reverse, (fun c => decide (c ≠ slashB)) x = true := by
    intro x hx; simp only [List.mem_reverse] at hx
    simp only [ne_eq, decide_eq_true_eq]; intro h; subst h; exact hb hx
  rw [List.takeWhile_append_of_pos h2]
  simp [slashB]

theorem parentOf_child (d b : GoString) (hb : slashB ∉ b) :
    parentOf (d ++ slashB :: b) = some d := by
  unfold parentOf
  simp only [baseOf_child d b hb]
  have : b.length < (d ++ slashB :: b).length := by simp; omega
  simp only [this, ↓reduceIte, Option.some.injEq]
  have hl : (d ++ slashB :: b).length - b.length - 1 = d.length := by simp; omega
  rw [hl]; simp

theorem parentOf_child' (d b : GoString) (hb : NameOk b) : parentOf (child d b) = some d :=
  parentOf_child d b hb.2.2.2.1

theorem baseOf_child' (d b : GoString) (hb : NameOk b) : baseOf (child d b) = b :=
  baseOf_child d b hb.2.2.2.1

theorem nameOk_noslash {cs : List GoString} (h : ∀ c ∈ cs, NameOk c) : ∀ c ∈ cs, slashB ∉ c :=
  fun c hc => (h c hc).2.2.2.1

theorem eq_of_nodup_map {α β : Type} {f : α → β} {a b : α} :
    ∀ {l : List α}, (l.map f).Nodup → a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, hn, ha, hb, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd he.symm (hn.1 b hb)
    · exact absurd he (hn.1 a ha)
    · exact eq_of_nodup_map hn.2 ha hb he

/-- Two roots of a well-formed list under which one path is canonical are the same root, and the
components agree. -/
theorem root_split_unique {roots : List (GoString × Ino)} (hr : RootsOk roots)
    {r r' : GoString × Ino} (h1 : r ∈ roots) (h2 : r' ∈ roots) {cs cs' : List GoString}
    (hc : ∀ c ∈ cs, NameOk c) (hc' : ∀ c ∈ cs', NameOk c)
    (he : joinPath r.1 cs = joinPath r'.1 cs') : r = r' ∧ cs = cs' := by
  obtain ⟨rcs, -, hrcs, hrf⟩ := (hr.2.2 r h1).1
  obtain ⟨rcs', -, hrcs', hrf'⟩ := (hr.2.2 r' h2).1
  have hall : rcs ++ cs = rcs' ++ cs' := by
    apply flatMap_slash_inj
    · intro c hc0; simp only [List.mem_append] at hc0
      rcases hc0 with h | h
      · exact (hrcs c h).2.2.2.1
      · exact (hc c h).2.2.2.1
    · intro c hc0; simp only [List.mem_append] at hc0
      rcases hc0 with h | h
      · exact (hrcs' c h).2.2.2.1
      · exact (hc' c h).2.2.2.1
    · have := he
      rw [hrf, hrf', ← joinPath_append, ← joinPath_append] at this
      simpa [joinPath] using this
  -- one root's components are a prefix of the other's
  have hpath : r.1 = r'.1 := by
    rcases List.append_eq_append_iff.1 hall with ⟨a, h3, h4⟩ | ⟨c, h3, h4⟩
    · -- rcs' = rcs ++ a
      refine Classical.byContradiction fun hne => ?_
      have hu : IsUnder r.1 r'.1 := by
        rw [hrf, hrf', h3, joinPath_append]
        rcases a with _ | ⟨x, a⟩
        · left; simp [joinPath]
        · right; exact ⟨x ++ a.flatMap (slashB :: ·), by simp [joinPath]⟩
      exact (hr.2.2 r h1).2 r' h2 hne hu
    · refine Classical.byContradiction fun hne => ?_
      have hu : IsUnder r'.1 r.1 := by
        rw [hrf, hrf', h3, joinPath_append]
        rcases c with _ | ⟨x, c⟩
        · left; simp [joinPath]
        · right; exact ⟨x ++ c.flatMap (slashB :: ·), by simp [joinPath]⟩
      exact (hr.2.2 r' h2).2 r h1 (Ne.symm hne) hu
  have hrr : r = r' := eq_of_nodup_map hr.1 h1 h2 hpath
  refine ⟨hrr, ?_⟩
  subst hrr
  exact joinPath_inj hc hc' he

/-- The path of components `cs` below a root names what walking them from the root names. -/
theorem lookup_joinPath {st : OsState} (hr : RootsOk st.fs.roots) {r : GoString} {j : Ino}
    (hrj : (r, j) ∈ st.fs.roots) {cs : List GoString} (hcs : ∀ c ∈ cs, NameOk c) :
    st.lookup (joinPath r cs) = walk st.tree (.dir j) cs := by
  unfold OsState.lookup
  have hex : ∃ (rj : GoString × Ino) (cs' : List GoString), rj ∈ st.fs.roots ∧
      (∀ c ∈ cs', NameOk c) ∧ joinPath r cs = joinPath rj.1 cs' := ⟨(r, j), cs, hrj, hcs, rfl⟩
  rw [dif_pos hex]
  have h1 := hex.choose_spec.choose_spec
  generalize hex.choose_spec.choose = cs0 at h1 ⊢
  generalize hex.choose = rj at h1 ⊢
  obtain ⟨h2, h3⟩ := root_split_unique hr h1.1 hrj h1.2.1 hcs h1.2.2.symm
  subst h2; subst h3; rfl

/-- What a path names, if anything, is named through a root: it is `joinPath r cs`. -/
theorem lookup_some {st : OsState} {p : GoString} {n : Node} (h : st.lookup p = some n) :
    ∃ r j cs, (r, j) ∈ st.fs.roots ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs ∧
      walk st.tree (.dir j) cs = some n := by
  unfold OsState.lookup at h
  split at h
  · rename_i hex
    have h1 := hex.choose_spec.choose_spec
    exact ⟨hex.choose.1, hex.choose.2, hex.choose_spec.choose, h1.1, h1.2.1, h1.2.2, h⟩
  · cases h

theorem walk_snoc (m : Tree) (n : Node) (cs : List GoString) (b : GoString) :
    walk m n (cs ++ [b]) = (walk m n cs).bind (fun n' => match n' with
      | .dir j => m.entry j b
      | .file _ => none) := by
  induction cs generalizing n with
  | nil =>
    cases n with
    | dir j =>
      show walk m (.dir j) [b] = m.entry j b
      cases h : m.entry j b <;> simp [walk, h]
    | file i => rfl
  | cons c cs ih =>
    cases n with
    | dir j =>
      simp only [List.cons_append, walk]
      cases m.entry j c with
      | none => rfl
      | some n' => exact ih n'
    | file i => rfl

/-- **The entry `b` of a directory `d`**: what `d`'s directory names `b`. -/
theorem lookup_child {st : OsState} (hr : RootsOk st.fs.roots) {d b : GoString} {j : Ino}
    (hd : st.lookup d = some (.dir j)) (hb : NameOk b) :
    st.lookup (child d b) = st.tree.entry j b := by
  obtain ⟨r, j0, cs, hrj, hcs, rfl, hw⟩ := lookup_some hd
  rw [← joinPath_snoc, lookup_joinPath hr hrj (by
    intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with h | rfl
    · exact hcs c h
    · exact hb), walk_snoc, hw]
  rfl

/-- The directory and name of `d/b`, for a directory `d`. -/
theorem parent_child {st : OsState} {d b : GoString} {j : Ino} (hd : st.lookup d = some (.dir j))
    (hb : NameOk b) : st.parent (child d b) = some (j, b) := by
  unfold OsState.parent
  rw [parentOf_child' d b hb]
  simp only [hd, baseOf_child' d b hb]

/-- `d/b` is a name of the tree, for a directory `d`. -/
theorem treeName_child {st : OsState} {d b : GoString} {j : Ino} (hd : st.lookup d = some (.dir j))
    (hb : NameOk b) : st.TreeName (child d b) := by
  obtain ⟨r, j0, cs, hrj, hcs, rfl, -⟩ := lookup_some hd
  refine ⟨(r, j0), hrj, cs ++ [b], by simp, ?_, (joinPath_snoc r cs b).symm⟩
  intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with h | rfl
  · exact hcs c h
  · exact hb

/-- A directory of the tree is a path of the tree. -/
theorem treePath_of_lookup {st : OsState} {d : GoString} {n : Node} (hd : st.lookup d = some n) :
    st.TreePath d := by
  obtain ⟨r, j0, cs, hrj, hcs, rfl, -⟩ := lookup_some hd
  rcases cs with _ | ⟨c, cs⟩
  · left; exact ⟨(r, j0), hrj, by simp [joinPath]⟩
  · right; exact ⟨(r, j0), hrj, c :: cs, by simp, hcs, rfl⟩


/-! ## Entries of a changed tree -/

theorem entry_upd (m : Tree) (j : Ino) (f : Dir → Dir) (j' : Ino) (b : GoString) :
    (m.upd j f).entry j' b = if j = j' then f ((m !! j).getD ∅) !! b else m.entry j' b := by
  unfold Tree.entry Tree.upd
  by_cases h : j = j'
  · subst h; simp
  · simp [h]

theorem getD_lookup (o : Option Dir) (b : GoString) : (o.getD ∅) !! b = o.bind (· !! b) := by
  cases o <;> rfl

theorem mem_upd (m : Tree) (j : Ino) (f : Dir → Dir) (x : Ino) :
    x ∈ m.upd j f ↔ j = x ∨ x ∈ m := by
  unfold Tree.upd
  rw [GMap.mem_iff, GMap.mem_iff]
  by_cases h : j = x
  · subst h; simp
  · simp [h]

theorem reach_mono {R : List (GoString × Ino)} {m m' : Tree}
    (h : ∀ j b j', m.entry j b = some (.dir j') → m'.entry j b = some (.dir j')) :
    ∀ {x}, Reach R m x → Reach R m' x := by
  intro x hx
  induction hx with
  | root r j hr => exact .root r j hr
  | child j b j' _ he ih => exact .child j b j' ih (h _ _ _ he)

/-- The entries of `m'` naming directories are `m`'s, and its keys `m`'s: a well-formed tree stays
one, if its new entries have valid names, an unreachable directory stays empty, and no file or
directory is named twice. -/
theorem treeWf_sameDirs {R : List (GoString × Ino)} {m m' : Tree} (hw : TreeWf R m)
    (hk : ∀ x, x ∈ m' ↔ x ∈ m)
    (hd : ∀ j b j', m'.entry j b = some (.dir j') ↔ m.entry j b = some (.dir j'))
    (hempty : ∀ x, ¬ Reach R m x → (∀ b, m.entry x b = none) → ∀ b, m'.entry x b = none)
    (hn : ∀ j b n, m'.entry j b = some n → NameOk b)
    (hu : ∀ j1 b1 j2 b2 n, m'.entry j1 b1 = some n → m'.entry j2 b2 = some n → j1 = j2 ∧ b1 = b2) :
    TreeWf R m' := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hw
  have hr : ∀ x, Reach R m' x ↔ Reach R m x := fun x =>
    ⟨reach_mono (fun j b j' h => (hd j b j').1 h), reach_mono (fun j b j' h => (hd j b j').2 h)⟩
  refine ⟨fun x hx => (hk x).2 (h1 x ((hr x).1 hx)), fun x hx => ?_, fun j b n he => ⟨hn j b n he, ?_⟩,
    fun j b j' he => h4 j b j' ((hd j b j').1 he), hu⟩
  · rcases h2 x ((hk x).1 hx) with h | ⟨he, hnn⟩
    · exact .inl ((hr x).2 h)
    · by_cases hrx : Reach R m x
      · exact .inl ((hr x).2 hrx)
      · exact .inr ⟨hempty x hrx he, fun j0 b0 h => hnn j0 b0 ((hd j0 b0 x).1 h)⟩
  · intro j' hj'
    cases n with
    | file i => simp [Node.dirIno] at hj'
    | dir j1 =>
      simp only [Node.dirIno, List.mem_singleton] at hj'; subst hj'
      exact (hk _).2 ((h3 j b _ ((hd j b _).1 he)).2 _ (by simp [Node.dirIno]))

/-! ## The operations that change no directory entry naming a directory -/

/-- A file created as `b` in the reachable directory `j`, where nothing is, of an inode no entry
names. -/
theorem treeWf_create {R : List (GoString × Ino)} {m : Tree} {j : Ino} {b : GoString} {i : Ino}
    (hw : TreeWf R m) (hj : Reach R m j) (hb : NameOk b) (he : m.entry j b = none)
    (hi : ¬ Named m i) : TreeWf R ((MetaOp.create j b i).apply m) := by
  simp only [MetaOp.apply]
  have hent : ∀ j' b', (m.upd j (fun d => <[b := Node.file i]> d)).entry j' b' =
      if j = j' ∧ b = b' then some (.file i) else m.entry j' b' := by
    intro j' b'
    rw [entry_upd]
    by_cases h1 : j = j'
    · subst h1
      by_cases h2 : b = b'
      · subst h2; simp
      · simp [h2, Tree.entry, getD_lookup]
    · simp [h1]
  refine treeWf_sameDirs hw (fun x => ?_) (fun j' b' j'' => ?_) (fun x hx _ b' => ?_)
    (fun j' b' n h => ?_) (fun j1 b1 j2 b2 n h1 h2 => ?_)
  · rw [mem_upd]; constructor
    · rintro (rfl | h); exact hw.1 _ hj; exact h
    · exact .inr
  · rw [hent]; split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [he]; simp
    · rfl
  · rw [hent]; split
    · rename_i h; obtain ⟨rfl, -⟩ := h; exact absurd hj hx
    · rename_i h; simp_all
  · rw [hent] at h; split at h
    · rename_i hh; obtain ⟨-, rfl⟩ := hh; exact hb
    · exact (hw.2.2.1 j' b' n h).1
  · rw [hent] at h1 h2
    split at h1 <;> split at h2
    · rename_i hh1 hh2; obtain ⟨rfl, rfl⟩ := hh1; obtain ⟨rfl, rfl⟩ := hh2; exact ⟨rfl, rfl⟩
    · cases h1; exact absurd ⟨j2, b2, h2⟩ hi
    · cases h2; exact absurd ⟨j1, b1, h1⟩ hi
    · exact hw.2.2.2.2 j1 b1 j2 b2 n h1 h2

/-- The file named `b` in `j` removed. -/
theorem treeWf_removeFile {R : List (GoString × Ino)} {m : Tree} {j : Ino} {b : GoString} {i : Ino}
    (hw : TreeWf R m) (hj : Reach R m j) (he : m.entry j b = some (.file i)) (n : Node) :
    TreeWf R ((MetaOp.remove j b n).apply m) := by
  simp only [MetaOp.apply]
  have hent : ∀ j' b', (m.upd j (fun d => GMap.delete b d)).entry j' b' =
      if j = j' ∧ b = b' then none else m.entry j' b' := by
    intro j' b'
    rw [entry_upd]
    by_cases h1 : j = j'
    · subst h1
      by_cases h2 : b = b'
      · subst h2; simp
      · simp [h2, Tree.entry, getD_lookup]
    · simp [h1]
  refine treeWf_sameDirs hw (fun x => ?_) (fun j' b' j'' => ?_) (fun x hx hn b' => ?_)
    (fun j' b' n h => ?_) (fun j1 b1 j2 b2 n h1 h2 => ?_)
  · rw [mem_upd]; constructor
    · rintro (rfl | h); exact hw.1 _ hj; exact h
    · exact .inr
  · rw [hent]; split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [he]; simp
    · rfl
  · rw [hent]; split
    · rfl
    · exact hn b'
  · rw [hent] at h; split at h
    · cases h
    · exact (hw.2.2.1 j' b' n h).1
  · rw [hent] at h1 h2
    split at h1 <;> split at h2
    · cases h1
    · cases h1
    · cases h2
    · exact hw.2.2.2.2 j1 b1 j2 b2 n h1 h2

/-- The file named `b` in `j0` renamed to `b'` in `j1` (replacing a file there, or nothing). -/
theorem treeWf_renameFile {R : List (GoString × Ino)} {m : Tree} {j0 j1 : Ino} {b b' : GoString}
    {i : Ino} (hw : TreeWf R m) (hj0 : Reach R m j0) (hj1 : Reach R m j1) (hb' : NameOk b')
    (he : m.entry j0 b = some (.file i)) (ht : ∀ j', m.entry j1 b' ≠ some (.dir j'))
    (n : Node) (old : Option Node) :
    TreeWf R ((MetaOp.rename j0 b j1 b' n old).apply m) := by
  simp only [MetaOp.apply, he]
  have hent : ∀ j' c, ((m.upd j0 (fun d => GMap.delete b d)).upd j1
      (fun d => <[b' := Node.file i]> d)).entry j' c =
      if j1 = j' ∧ b' = c then some (.file i)
      else if j0 = j' ∧ b = c then none else m.entry j' c := by
    intro j' c
    rw [entry_upd]
    by_cases h1 : j1 = j'
    · subst h1
      by_cases h2 : b' = c
      · subst h2; simp
      · simp only [h2, and_false, ↓reduceIte]
        rw [GMap.lookup_insert_ne _ _ h2, getD_lookup]
        show (m.upd j0 (fun d => GMap.delete b d)).entry j1 c = _
        rw [entry_upd]
        by_cases h3 : j0 = j1
        · subst h3
          by_cases h4 : b = c
          · subst h4; simp
          · simp [h4, Tree.entry, getD_lookup]
        · simp [h3]
    · simp only [h1, false_and, ↓reduceIte]
      rw [entry_upd]
      by_cases h3 : j0 = j'
      · subst h3
        by_cases h4 : b = c
        · subst h4; simp
        · simp [h4, Tree.entry, getD_lookup]
      · simp [h3]
  refine treeWf_sameDirs hw (fun x => ?_) (fun j' c j'' => ?_) (fun x hx hn c => ?_)
    (fun j' c n h => ?_) (fun ja ba jb bb n h1 h2 => ?_)
  · rw [mem_upd, mem_upd]; constructor
    · rintro (rfl | rfl | h); exact hw.1 _ hj1; exact hw.1 _ hj0; exact h
    · exact fun h => .inr (.inr h)
  · rw [hent]; split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; simp [ht]
    · split
      · rename_i _ h; obtain ⟨rfl, rfl⟩ := h; rw [he]; simp
      · rfl
  · rw [hent]; split
    · rename_i h; obtain ⟨rfl, -⟩ := h; exact absurd hj1 hx
    · split
      · rfl
      · exact hn c
  · rw [hent] at h; split at h
    · rename_i hh; obtain ⟨-, rfl⟩ := hh; exact hb'
    · split at h
      · cases h
      · exact (hw.2.2.1 j' c n h).1
  · rw [hent] at h1 h2
    split at h1 <;> split at h2
    · rename_i hh1 hh2; obtain ⟨rfl, rfl⟩ := hh1; obtain ⟨rfl, rfl⟩ := hh2; exact ⟨rfl, rfl⟩
    · cases h1
      split at h2
      · cases h2
      · rename_i hn2; obtain ⟨rfl, rfl⟩ := hw.2.2.2.2 _ _ _ _ _ h2 he
        exact absurd ⟨rfl, rfl⟩ hn2
    · cases h2
      split at h1
      · cases h1
      · rename_i hn1; obtain ⟨rfl, rfl⟩ := hw.2.2.2.2 _ _ _ _ _ h1 he
        exact absurd ⟨rfl, rfl⟩ hn1
    · split at h1
      · cases h1
      · split at h2
        · cases h2
        · exact hw.2.2.2.2 _ _ _ _ _ h1 h2

/-! ## The operations that change entries naming directories -/

/-- `x` is in the subtree of `J` (or is `J`): walking down entries naming directories. -/
inductive BelowP (m : Tree) : Ino → Ino → Prop where
  | self (J : Ino) : BelowP m J J
  | step (J : Ino) (c : GoString) (J' x : Ino) :
      m.entry J c = some (.dir J') → BelowP m J' x → BelowP m J x

theorem BelowP.snoc {m : Tree} {J y x : Ino} {c : GoString} (h : BelowP m J y)
    (he : m.entry y c = some (.dir x)) : BelowP m J x := by
  induction h with
  | self J => exact .step J c x x he (.self x)
  | step J c' J' y he' _ ih => exact .step J c' J' x he' (ih he)

theorem treeWf_named_mem {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {j : Ino}
    {b : GoString} {x : Ino} (he : m.entry j b = some (.dir x)) : x ∈ m :=
  (hw.2.2.1 j b _ he).2 x (by simp [Node.dirIno])

theorem not_named_of_not_mem {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {x : Ino}
    (hx : x ∉ m) : ∀ j b, m.entry j b ≠ some (.dir x) :=
  fun _ _ he => hx (treeWf_named_mem hw he)

theorem entry_none_of_not_mem {m : Tree} {x : Ino} (hx : x ∉ m) (b : GoString) :
    m.entry x b = none := by
  unfold Tree.entry
  rw [GMap.mem_iff] at hx
  cases h : m !! x with
  | none => rfl
  | some d => rw [h] at hx; exact absurd rfl hx

/-- A new, empty directory `j'` (an inode not in the tree, of no root) made as `b` in the reachable
directory `j`, where nothing is. -/
theorem treeWf_mkdir {R : List (GoString × Ino)} {m : Tree} {j : Ino} {b : GoString} {j' : Ino}
    (hw : TreeWf R m) (hj : Reach R m j) (hb : NameOk b) (he : m.entry j b = none)
    (hj' : j' ∉ m) (hr : ∀ r, (r, j') ∉ R) : TreeWf R ((MetaOp.mkdir j b j').apply m) := by
  simp only [MetaOp.apply]
  have hjm : j ∈ m := hw.1 _ hj
  have hne : j ≠ j' := fun h => hj' (h ▸ hjm)
  have hent : ∀ x c, Tree.entry (<[j' := (∅ : Dir)]> (m.upd j (fun d => <[b := Node.dir j']> d)) : Tree) x c =
      if x = j' then none else if j = x ∧ b = c then some (.dir j') else m.entry x c := by
    intro x c
    by_cases hx : x = j'
    · subst hx; simp [Tree.entry]
    · simp only [hx, ↓reduceIte]
      unfold Tree.entry; rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      show (m.upd j (fun d => <[b := Node.dir j']> d)).entry x c = _
      rw [entry_upd]
      by_cases h1 : j = x
      · subst h1
        by_cases h2 : b = c
        · subst h2; simp
        · simp [h2, Tree.entry, getD_lookup]
      · simp [h1, Tree.entry]
  have hmem : ∀ x, x ∈ <[j' := (∅ : Dir)]> (m.upd j (fun d => <[b := Node.dir j']> d)) ↔
      x = j' ∨ x ∈ m := by
    intro x; rw [GMap.mem_iff]
    by_cases hx : j' = x
    · subst hx; simp
    · simp only [GMap.lookup_insert_eq_iff, hx, ↓reduceIte, Ne.symm hx, false_or]
      rw [← GMap.mem_iff, mem_upd]
      constructor
      · rintro (rfl | h); exact hjm; exact h
      · exact .inr
  have hnn := not_named_of_not_mem hw hj'
  -- reachability: the old one, and `j'`
  have hold : ∀ x c y, m.entry x c = some (.dir y) →
      Tree.entry (<[j' := (∅ : Dir)]> (m.upd j (fun d => <[b := Node.dir j']> d)) : Tree) x c = some (.dir y) := by
    intro x c y h
    rw [hent]
    have hx : x ≠ j' := fun hx => by subst hx; rw [entry_none_of_not_mem hj'] at h; cases h
    rw [if_neg hx]; split
    · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; rw [he] at h; cases h
    · exact h
  have hreach : ∀ x, Reach R (<[j' := (∅ : Dir)]> (m.upd j (fun d => <[b := Node.dir j']> d))) x ↔
      Reach R m x ∨ x = j' := by
    intro x; constructor
    · intro h
      induction h with
      | root r x hr => exact .inl (.root r x hr)
      | child y c x' _ hy ih =>
        rw [hent] at hy
        split at hy
        · cases hy
        · split at hy
          · rename_i hh; cases hy; exact .inr rfl
          · rcases ih with ih | rfl
            · exact .inl (.child y c x' ih hy)
            · rw [entry_none_of_not_mem hj'] at hy; cases hy
    · rintro (h | h)
      · exact reach_mono hold h
      · rw [h]; exact .child j b j' (reach_mono hold hj) (by rw [hent]; simp [hne])
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x c n h => ?_, fun x c y h => ?_,
    fun x1 c1 x2 c2 n h1 h2 => ?_⟩
  · rcases (hreach x).1 hx with h | rfl
    · exact (hmem x).2 (.inr (hw.1 x h))
    · exact (hmem _).2 (.inl rfl)
  · rcases (hmem x).1 hx with rfl | hx
    · exact .inl ((hreach _).2 (.inr rfl))
    · by_cases hrx : Reach R m x
      · exact .inl ((hreach x).2 (.inl hrx))
      · obtain ⟨hemp, hun⟩ : (∀ c, m.entry x c = none) ∧ ∀ x0 c0, m.entry x0 c0 ≠ some (.dir x) := by
          rcases hw.2.1 x hx with h | h
          · exact absurd h hrx
          · exact h
        have hxj : j ≠ x := fun h => hrx (h ▸ hj)
        have hxj' : x ≠ j' := fun h => hj' (h ▸ hx)
        refine .inr ⟨fun c => ?_, fun x0 c0 h0 => ?_⟩
        · rw [hent, if_neg hxj', if_neg (fun h => hxj h.1)]; exact hemp c
        · rw [hent] at h0
          split at h0
          · cases h0
          · split at h0
            · cases h0; exact hxj' rfl
            · exact hun x0 c0 h0
  · rw [hent] at h; split at h
    · cases h
    · split at h
      · rename_i hh; obtain ⟨-, rfl⟩ := hh; cases h
        exact ⟨hb, fun y hy => by simp [Node.dirIno] at hy; subst hy; exact (hmem _).2 (.inl rfl)⟩
      · refine ⟨(hw.2.2.1 x c n h).1, fun y hy => (hmem y).2 (.inr ((hw.2.2.1 x c n h).2 y hy))⟩
  · rw [hent] at h; split at h
    · cases h
    · split at h
      · cases h; exact hr
      · exact hw.2.2.2.1 x c y h
  · rw [hent] at h1 h2
    split at h1; · cases h1
    split at h2; · cases h2
    split at h1 <;> split at h2
    · rename_i hh1 hh2; obtain ⟨rfl, rfl⟩ := hh1; obtain ⟨rfl, rfl⟩ := hh2; exact ⟨rfl, rfl⟩
    · cases h1; exact absurd h2 (hnn x2 c2)
    · cases h2; exact absurd h1 (hnn x1 c1)
    · exact hw.2.2.2.2 x1 c1 x2 c2 n h1 h2

/-- The empty directory `J` named `b` in the reachable directory `j` removed: `J` stays, empty and
named by no entry (`TreeWf`'s removed directories). -/
theorem treeWf_rmdir {R : List (GoString × Ino)} {m : Tree} {j : Ino} {b : GoString} {J : Ino}
    (hw : TreeWf R m) (hj : Reach R m j) (he : m.entry j b = some (.dir J))
    (hemp : ∀ c, m.entry J c = none) (n : Node) :
    TreeWf R ((MetaOp.remove j b n).apply m) := by
  simp only [MetaOp.apply]
  have hent : ∀ x c, (m.upd j (fun d => GMap.delete b d)).entry x c =
      if j = x ∧ b = c then none else m.entry x c := by
    intro x c
    rw [entry_upd]
    by_cases h1 : j = x
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp
      · simp [h2, Tree.entry, getD_lookup]
    · simp [h1]
  have hjm : j ∈ m := hw.1 _ hj
  have hJr : ∀ r, (r, J) ∉ R := hw.2.2.2.1 j b J he
  have hJj : J ≠ j := fun h => by subst h; rw [hemp b] at he; cases he
  -- only `(j, b)` named `J`
  have honly : ∀ x c, m.entry x c = some (.dir J) → x = j ∧ c = b := fun x c h =>
    hw.2.2.2.2 x c j b _ h he
  have hsub : ∀ x c y, (m.upd j (fun d => GMap.delete b d)).entry x c = some (.dir y) →
      m.entry x c = some (.dir y) := by
    intro x c y h; rw [hent] at h; split at h
    · cases h
    · exact h
  have hreach : ∀ x, Reach R (m.upd j (fun d => GMap.delete b d)) x ↔ Reach R m x ∧ x ≠ J := by
    intro x; constructor
    · intro h
      refine ⟨reach_mono hsub h, ?_⟩
      intro hx; subst hx
      cases h with
      | root r _ hr => exact hJr r hr
      | child y c _ _ hy =>
        have := hsub _ _ _ hy
        obtain ⟨rfl, rfl⟩ := honly y c this
        rw [hent] at hy; simp at hy
    · rintro ⟨h, hx⟩
      induction h with
      | root r x hr => exact .root r x hr
      | child y c x' hyr hy ih =>
        have hyJ : y ≠ J := fun h => by subst h; rw [hemp c] at hy; cases hy
        refine .child y c x' (ih hyJ) ?_
        rw [hent, if_neg]
        · exact hy
        · rintro ⟨rfl, rfl⟩; rw [he] at hy; cases hy; exact hx rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x c n h => ?_, fun x c y h => ?_,
    fun x1 c1 x2 c2 n h1 h2 => ?_⟩
  · rw [mem_upd]; exact .inr (hw.1 x ((hreach x).1 hx).1)
  · rw [mem_upd] at hx
    have hxm : x ∈ m := by rcases hx with rfl | h; exact hjm; exact h
    by_cases hxJ : x = J
    · subst hxJ
      refine .inr ⟨fun c => by rw [hent, if_neg (fun h => hJj h.1.symm)]; exact hemp c,
        fun x0 c0 h0 => ?_⟩
      obtain ⟨rfl, rfl⟩ := honly x0 c0 (hsub _ _ _ h0)
      rw [hent] at h0; simp at h0
    · by_cases hrx : Reach R m x
      · exact .inl ((hreach x).2 ⟨hrx, hxJ⟩)
      · obtain ⟨hem, hun⟩ : (∀ c, m.entry x c = none) ∧ ∀ x0 c0, m.entry x0 c0 ≠ some (.dir x) := by
          rcases hw.2.1 x hxm with h | h
          · exact absurd h hrx
          · exact h
        have hxj : j ≠ x := fun h => hrx (h ▸ hj)
        exact .inr ⟨fun c => by rw [hent, if_neg (fun h => hxj h.1)]; exact hem c,
          fun x0 c0 h0 => hun x0 c0 (hsub _ _ _ h0)⟩
  · rw [hent] at h; split at h
    · cases h
    · refine ⟨(hw.2.2.1 x c n h).1, fun y hy => ?_⟩
      rw [mem_upd]; exact .inr ((hw.2.2.1 x c n h).2 y hy)
  · exact hw.2.2.2.1 x c y (hsub _ _ _ h)
  · rw [hent] at h1 h2
    split at h1
    · cases h1
    · split at h2
      · cases h2
      · exact hw.2.2.2.2 x1 c1 x2 c2 n h1 h2

/-! ## Paths are unique; a rename of a directory -/

theorem walk_append (m : Tree) (n : Node) (a c : List GoString) :
    walk m n (a ++ c) = (walk m n a).bind (fun n' => walk m n' c) := by
  induction a generalizing n with
  | nil => rfl
  | cons x a ih =>
    cases n with
    | dir j =>
      simp only [List.cons_append, walk]
      cases m.entry j x with
      | none => rfl
      | some n' => exact ih n'
    | file i => rfl

theorem belowP_of_walk {m : Tree} : ∀ {ds : List GoString} {J x : Ino},
    walk m (.dir J) ds = some (.dir x) → BelowP m J x
  | [], J, x, h => by simp [walk] at h; subst h; exact .self _
  | c :: ds, J, x, h => by
    simp only [walk] at h
    cases he : m.entry J c with
    | none => rw [he] at h; cases h
    | some n =>
      rw [he] at h; simp only at h
      cases n with
      | dir J' => exact .step J c J' x he (belowP_of_walk h)
      | file i => cases ds <;> simp [walk] at h

theorem walk_of_belowP {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {J x : Ino}
    (h : BelowP m J x) : ∃ ds, (∀ d ∈ ds, NameOk d) ∧ walk m (.dir J) ds = some (.dir x) := by
  induction h with
  | self J => exact ⟨[], by simp, rfl⟩
  | step J c J' x he _ ih =>
    obtain ⟨ds, hds, hw'⟩ := ih
    refine ⟨c :: ds, ?_, by simp only [walk, he]; exact hw'⟩
    intro d hd; simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact (hw.2.2.1 J d _ he).1
    · exact hds d hd

theorem walk_last {m : Tree} {n : Node} {cs : List GoString} {x : Ino} (hne : cs ≠ [])
    (h : walk m n cs = some (.dir x)) :
    ∃ y, walk m n cs.dropLast = some (.dir y) ∧ m.entry y (cs.getLast hne) = some (.dir x) := by
  have hcs := List.dropLast_concat_getLast hne
  rw [← hcs, walk_snoc] at h
  cases hw : walk m n cs.dropLast with
  | none => rw [hw] at h; cases h
  | some n' =>
    rw [hw] at h
    cases n' with
    | dir y => exact ⟨y, rfl, h⟩
    | file i => cases h

/-- **A directory has one path from the roots**: its inode, and the components. -/
theorem path_unique {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) :
    ∀ (n : Nat) {r1 r2 : GoString} {j1 j2 x : Ino} {cs1 cs2 : List GoString},
      cs1.length + cs2.length ≤ n → (r1, j1) ∈ R → (r2, j2) ∈ R →
      walk m (.dir j1) cs1 = some (.dir x) → walk m (.dir j2) cs2 = some (.dir x) →
      j1 = j2 ∧ cs1 = cs2 := by
  intro n
  induction n with
  | zero =>
    intro r1 r2 j1 j2 x cs1 cs2 hl _ _ h1 h2
    have h1' : cs1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2' : cs2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1' h2'
    simp [walk] at h1 h2; subst h1 h2; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro r1 r2 j1 j2 x cs1 cs2 hl hr1 hr2 h1 h2
    by_cases e1 : cs1 = [] <;> by_cases e2 : cs2 = []
    · subst e1 e2; simp [walk] at h1 h2; subst h1 h2; exact ⟨rfl, rfl⟩
    · subst e1; simp [walk] at h1; subst h1
      obtain ⟨y, -, hy⟩ := walk_last e2 h2
      exact absurd hr1 (hw.2.2.2.1 _ _ _ hy r1)
    · subst e2; simp [walk] at h2; subst h2
      obtain ⟨y, -, hy⟩ := walk_last e1 h1
      exact absurd hr2 (hw.2.2.2.1 _ _ _ hy r2)
    · obtain ⟨y1, hw1, hy1⟩ := walk_last e1 h1
      obtain ⟨y2, hw2, hy2⟩ := walk_last e2 h2
      obtain ⟨rfl, hc⟩ := hw.2.2.2.2 _ _ _ _ _ hy1 hy2
      have hl1 := List.length_dropLast (xs := cs1)
      have hl2 := List.length_dropLast (xs := cs2)
      have hp1 : 0 < cs1.length := List.length_pos_iff.2 e1
      have hp2 : 0 < cs2.length := List.length_pos_iff.2 e2
      obtain ⟨rfl, hd⟩ := ih (by omega) hr1 hr2 hw1 hw2
      refine ⟨rfl, ?_⟩
      rw [← List.dropLast_concat_getLast e1, ← List.dropLast_concat_getLast e2, hd, hc]

/-- A directory below the directory at `s` is at a path under `s`. -/
theorem isUnder_of_belowP {st : OsState} (hr : RootsOk st.fs.roots) (hw : TreeWf st.fs.roots st.tree)
    {s p : GoString} {J x : Ino} (hs : st.lookup s = some (.dir J)) (hp : st.lookup p = some (.dir x))
    (hb : BelowP st.tree J x) : IsUnder s p := by
  obtain ⟨r, j, cs, hrj, hcs, rfl, hw1⟩ := lookup_some hs
  obtain ⟨r', j', cs', hrj', hcs', rfl, hw2⟩ := lookup_some hp
  obtain ⟨ds, hds, hw3⟩ := walk_of_belowP hw hb
  have hw4 : walk st.tree (.dir j) (cs ++ ds) = some (.dir x) := by
    rw [walk_append, hw1]; exact hw3
  obtain ⟨rfl, hc⟩ := path_unique hw _ (Nat.le_refl _) hrj hrj' hw4 hw2
  have : r = r' := by
    have := eq_of_nodup_map (f := (·.2)) hr.2.1 hrj hrj' rfl
    simp only [Prod.mk.injEq] at this; exact this.1
  subst this; subst hc
  rw [joinPath_append]
  rcases ds with _ | ⟨d, ds⟩
  · left; simp [joinPath]
  · right; exact ⟨d ++ ds.flatMap (slashB :: ·), by simp [joinPath]⟩

/-- The directory `J` named `b` in the reachable `j0` renamed to `b'` in the reachable `j1`, not in
`J`'s subtree, onto nothing or an empty directory. -/
theorem treeWf_renameDir {R : List (GoString × Ino)} {m : Tree} {j0 j1 J : Ino} {b b' : GoString}
    (hw : TreeWf R m) (hj0 : Reach R m j0) (hj1 : Reach R m j1) (hb' : NameOk b')
    (he : m.entry j0 b = some (.dir J)) (hne : ¬ (j0 = j1 ∧ b = b'))
    (ht : m.entry j1 b' = none ∨ ∃ J2, m.entry j1 b' = some (.dir J2) ∧ ∀ c, m.entry J2 c = none)
    (hnot : ¬ BelowP m J j1) (n : Node) (old : Option Node) :
    TreeWf R ((MetaOp.rename j0 b j1 b' n old).apply m) := by
  simp only [MetaOp.apply, he]
  generalize hm' : (m.upd j0 (fun d => GMap.delete b d)).upd j1 (fun d => <[b' := Node.dir J]> d) = m'
  have hent : ∀ x c, m'.entry x c =
      if j1 = x ∧ b' = c then some (.dir J)
      else if j0 = x ∧ b = c then none else m.entry x c := by
    intro x c; rw [← hm', entry_upd]
    by_cases h1 : j1 = x
    · subst h1
      by_cases h2 : b' = c
      · subst h2; simp
      · simp only [h2, and_false, ↓reduceIte]
        rw [GMap.lookup_insert_ne _ _ h2, getD_lookup]
        show (m.upd j0 (fun d => GMap.delete b d)).entry j1 c = _
        rw [entry_upd]
        by_cases h3 : j0 = j1
        · subst h3
          by_cases h4 : b = c
          · subst h4; simp
          · simp [h4, Tree.entry, getD_lookup]
        · simp [h3]
    · simp only [h1, false_and, ↓reduceIte]
      rw [entry_upd]
      by_cases h3 : j0 = x
      · subst h3
        by_cases h4 : b = c
        · subst h4; simp
        · simp [h4, Tree.entry, getD_lookup]
      · simp [h3]
  have hj0m := hw.1 _ hj0
  have hj1m := hw.1 _ hj1
  have hmem : ∀ x, x ∈ m' ↔ x ∈ m := by
    intro x; rw [← hm', mem_upd, mem_upd]; constructor
    · rintro (rfl | rfl | h); exact hj1m; exact hj0m; exact h
    · exact fun h => .inr (.inr h)
  have honlyJ : ∀ x c, m.entry x c = some (.dir J) → x = j0 ∧ c = b := fun x c h =>
    hw.2.2.2.2 x c j0 b _ h he
  -- the replaced directory, if any
  have hJ2 : ∀ J2, m.entry j1 b' = some (.dir J2) → (∀ c, m.entry J2 c = none) := by
    intro J2 h; rcases ht with ht | ⟨J2', h', hemp⟩
    · rw [ht] at h; cases h
    · rw [h'] at h; cases h; exact hemp
  have hJne : ∀ J2, m.entry j1 b' = some (.dir J2) → J ≠ J2 := by
    intro J2 h hJ; subst hJ; exact hne (by obtain ⟨h1, h2⟩ := honlyJ _ _ h; exact ⟨h1.symm, h2.symm⟩)
  have hJr : ∀ r, (r, J) ∉ R := hw.2.2.2.1 j0 b J he
  -- reachability
  have hA : ∀ x, Reach R m x → ¬ BelowP m J x → (∀ J2, m.entry j1 b' = some (.dir J2) → x ≠ J2) →
      Reach R m' x := by
    intro x hx
    induction hx with
    | root r x hr => intro _ _; exact .root r x hr
    | child y c x' hyr hy ih =>
      intro hnb hnj
      have hyb : ¬ BelowP m J y := fun h => hnb (h.snoc hy)
      have hyj : ∀ J2, m.entry j1 b' = some (.dir J2) → y ≠ J2 := by
        intro J2 h2 hy2; subst hy2; rw [hJ2 _ h2 c] at hy; cases hy
      refine .child y c x' (ih hyb hyj) ?_
      rw [hent]
      rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hnj x' hy rfl)]
      rw [if_neg (by rintro ⟨rfl, rfl⟩; rw [he] at hy; cases hy; exact hnb (.self _))]
      exact hy
  have hRJ : Reach R m' J := by
    have hj1J2 : ∀ J2, m.entry j1 b' = some (.dir J2) → j1 ≠ J2 := by
      intro J2 h2 h; subst h; rw [hJ2 _ h2 b'] at h2; cases h2
    exact .child j1 b' J (hA j1 hj1 hnot hj1J2) (by rw [hent]; simp)
  have hC : ∀ J0 x, BelowP m J0 x → BelowP m J J0 → Reach R m' J0 → Reach R m' x := by
    intro J0 x hb
    induction hb with
    | self J0 => intro _ h; exact h
    | step J0 c J'' x he' _ ih =>
      intro hbJ hr0
      apply ih (hbJ.snoc he')
      by_cases h1 : j1 = J0 ∧ b' = c
      · obtain ⟨rfl, rfl⟩ := h1; exact absurd hbJ hnot
      by_cases h2 : j0 = J0 ∧ b = c
      · obtain ⟨rfl, rfl⟩ := h2; rw [he] at he'; cases he'; exact hRJ
      · exact .child J0 c J'' hr0 (by rw [hent, if_neg h1, if_neg h2]; exact he')
  have hreach : ∀ x, Reach R m' x ↔
      Reach R m x ∧ ∀ J2, m.entry j1 b' = some (.dir J2) → x ≠ J2 := by
    intro x; constructor
    · intro h
      induction h with
      | root r x hr =>
        refine ⟨.root r x hr, fun J2 h2 hx => ?_⟩; subst hx
        exact hw.2.2.2.1 j1 b' _ h2 r hr
      | child y c x' _ hy ih =>
        rw [hent] at hy
        split at hy
        · cases hy
          exact ⟨.child j0 b J hj0 he, hJne⟩
        · split at hy
          · cases hy
          · rename_i hn1 hn2
            refine ⟨.child y c x' ih.1 hy, fun J2 h2 hx => ?_⟩; subst hx
            obtain ⟨rfl, rfl⟩ := hw.2.2.2.2 _ _ _ _ _ hy h2
            exact hn1 ⟨rfl, rfl⟩
    · rintro ⟨h, hn2⟩
      by_cases hb : BelowP m J x
      · exact hC J x hb (.self J) hRJ
      · exact hA x h hb hn2
  refine ⟨fun x hx => (hmem x).2 (hw.1 x ((hreach x).1 hx).1), fun x hx => ?_,
    fun x c n h => ?_, fun x c y h => ?_, fun x1 c1 x2 c2 n h1 h2 => ?_⟩
  · have hxm := (hmem x).1 hx
    by_cases hx2 : ∃ J2, m.entry j1 b' = some (.dir J2) ∧ x = J2
    · obtain ⟨J2, h2, rfl⟩ := hx2
      have hemp := hJ2 _ h2
      have hx0 : j0 ≠ x := fun h => by subst h; rw [hemp b] at he; cases he
      have hx1 : j1 ≠ x := fun h => by subst h; rw [hemp b'] at h2; cases h2
      refine .inr ⟨fun c => ?_, fun x0 c0 h0 => ?_⟩
      · rw [hent, if_neg (fun h => hx1 h.1), if_neg (fun h => hx0 h.1)]; exact hemp c
      rw [hent] at h0; split at h0
      · cases h0; exact hJne _ h2 rfl
      · split at h0
        · cases h0
        · rename_i hn1 _
          obtain ⟨rfl, rfl⟩ := hw.2.2.2.2 _ _ _ _ _ h0 h2
          exact hn1 ⟨rfl, rfl⟩
    · have hnj : ∀ J2, m.entry j1 b' = some (.dir J2) → x ≠ J2 := fun J2 h2 hx => hx2 ⟨J2, h2, hx⟩
      by_cases hrx : Reach R m x
      · exact .inl ((hreach x).2 ⟨hrx, hnj⟩)
      · obtain ⟨hem, hun⟩ : (∀ c, m.entry x c = none) ∧ ∀ x0 c0, m.entry x0 c0 ≠ some (.dir x) := by
          rcases hw.2.1 x hxm with h | h
          · exact absurd h hrx
          · exact h
        have hx0 : j0 ≠ x := fun h => hrx (h ▸ hj0)
        have hx1 : j1 ≠ x := fun h => hrx (h ▸ hj1)
        refine .inr ⟨fun c => ?_, fun x0 c0 h0 => ?_⟩
        · rw [hent, if_neg (fun h => hx1 h.1), if_neg (fun h => hx0 h.1)]; exact hem c
        rw [hent] at h0; split at h0
        · cases h0; exact hrx (.child j0 b J hj0 he)
        · split at h0
          · cases h0
          · exact hun x0 c0 h0
  · rw [hent] at h; split at h
    · rename_i hh; obtain ⟨-, rfl⟩ := hh; cases h
      exact ⟨hb', fun y hy => by
        simp [Node.dirIno] at hy; subst hy; exact (hmem _).2 (treeWf_named_mem hw he)⟩
    · split at h
      · cases h
      · exact ⟨(hw.2.2.1 x c n h).1, fun y hy => (hmem y).2 ((hw.2.2.1 x c n h).2 y hy)⟩
  · rw [hent] at h; split at h
    · cases h; exact hJr
    · split at h
      · cases h
      · exact hw.2.2.2.1 x c y h
  · rw [hent] at h1 h2
    split at h1 <;> split at h2
    · rename_i hh1 hh2; obtain ⟨rfl, rfl⟩ := hh1; obtain ⟨rfl, rfl⟩ := hh2; exact ⟨rfl, rfl⟩
    · cases h1
      split at h2
      · cases h2
      · rename_i hn2; obtain ⟨rfl, rfl⟩ := honlyJ _ _ h2; exact absurd ⟨rfl, rfl⟩ hn2
    · cases h2
      split at h1
      · cases h1
      · rename_i hn1; obtain ⟨rfl, rfl⟩ := honlyJ _ _ h1; exact absurd ⟨rfl, rfl⟩ hn1
    · split at h1
      · cases h1
      · split at h2
        · cases h2
        · exact hw.2.2.2.2 _ _ _ _ _ h1 h2
end Fs
end Perennial

end
