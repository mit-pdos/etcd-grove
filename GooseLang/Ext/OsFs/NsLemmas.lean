/-
Pure laws of the namespace's ghost state (`Ghost.lean`'s `NsWf`, `NsCoh`) for the specs of
`NsSpecs.lean`: paths of a directory's entries, a directory's changes (`DirG.push`), and the
coherence kept by a file operation of a directory its holder holds whole. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.Ghost

@[expose] public section

noncomputable section

namespace Perennial

/-! ## Paths -/

/-- The entry `b` of the directory `d`. -/
abbrev child (d b : GoString) : GoString := d ++ slashB :: b

theorem joinPath_snoc (r : GoString) (cs : List GoString) (b : GoString) :
    joinPath r (cs ++ [b]) = child (joinPath r cs) b := by
  simp [joinPath, List.flatMap_append]

theorem nul_not_mem_joinPath {r : GoString} {cs : List GoString} (hr : nulB ∉ r)
    (hcs : ∀ c ∈ cs, NameOk c) : nulB ∉ joinPath r cs := by
  unfold joinPath
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, not_or, not_exists, not_and]
  refine ⟨hr, fun c hc => ⟨by decide, (hcs c hc).2.2.2.2⟩⟩

theorem nul_not_mem_root {r : GoString} (h : RootForm r) : nulB ∉ r := by
  obtain ⟨cs, -, hcs, rfl⟩ := h
  exact nul_not_mem_joinPath (by simp) hcs

theorem canonBelow_child {r d b : GoString} (hd : d = r ∨ CanonBelow r d) (hb : NameOk b) :
    CanonBelow r (child d b) := by
  rcases hd with rfl | ⟨cs, _, hcs, rfl⟩
  · exact ⟨[b], by simp, by simpa using hb, by simp [joinPath]⟩
  · refine ⟨cs ++ [b], by simp, ?_, (joinPath_snoc r cs b).symm⟩
    intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hcs c hc
    · exact hb

theorem isUnder_of_canonBelow {r p : GoString} (h : CanonBelow r p) : IsUnder r p := by
  obtain ⟨cs, hne, -, rfl⟩ := h
  right
  cases cs with
  | nil => exact absurd rfl hne
  | cons c cs => exact ⟨c ++ cs.flatMap (fun c => slashB :: c), by simp [joinPath]⟩

theorem nul_not_mem_canonBelow {r p : GoString} (hr : RootForm r) (h : CanonBelow r p) :
    nulB ∉ p := by
  obtain ⟨cs, -, hcs, rfl⟩ := h
  exact nul_not_mem_joinPath (nul_not_mem_root hr) hcs

theorem entsOf_child (m : NsMap) (d b : GoString) (hb : NameOk b) :
    entsOf m d !! b = m !! child d b := by
  rw [entsOf_lookup, if_pos hb]

theorem parentOf_child' (d b : GoString) (hb : NameOk b) : parentOf (child d b) = some d :=
  parentOf_child d b hb.2.2.2.1

theorem baseOf_child' (d b : GoString) (hb : NameOk b) : baseOf (child d b) = b :=
  baseOf_child d b hb.2.2.2.1

/-! ## The current namespace -/

section current
variable {st : OsState}

theorem NsWf.shape (hw : NsWf st) : NsShape st.roots st.ns := by
  have h := (hw.hist st.nsLog.length (Nat.le_refl _)).1
  rwa [List.take_length, ← hw.replay] at h

theorem NsWf.keys (hw : NsWf st) {p k : GoString} (h : st.ns !! p = some (.file k)) :
    IsInoKey k ∧ ∃ f, st.files !! k = some (some f) := by
  have h' := (hw.hist st.nsLog.length (Nat.le_refl _)).2
  rw [List.take_length, ← hw.replay] at h'
  exact h' p k h

/-- A directory of the namespace is a root or canonical below one. -/
theorem NsWf.dir_form (hw : NsWf st) {d : GoString} (hd : st.ns !! d = some .dir) :
    ∃ r ∈ st.roots, d = r ∨ CanonBelow r d := by
  rcases hw.shape.2.1 d .dir hd with h | ⟨⟨r, hr, hc⟩, -⟩
  · exact ⟨d, h, .inl rfl⟩
  · exact ⟨r, hr, .inr hc⟩

theorem NsWf.nsName_child (hw : NsWf st) {d b : GoString} (hd : st.ns !! d = some .dir)
    (hb : NameOk b) : st.NsName (child d b) := by
  obtain ⟨r, hr, hdr⟩ := hw.dir_form hd
  exact ⟨r, hr, canonBelow_child hdr hb⟩

theorem NsWf.nsPath_dir (hw : NsWf st) {d : GoString} (hd : st.ns !! d = some .dir) :
    st.NsPath d := by
  obtain ⟨r, hr, rfl | hc⟩ := hw.dir_form hd
  · exact .inl hr
  · exact .inr ⟨r, hr, hc⟩

/-- A path of the namespace is no key of `files`: no legacy path is in a root's tree, and no
key of a file of the namespace is a path (it has a NUL byte). -/
theorem NsWf.not_files (hw : NsWf st) {r p : GoString} (hr : r ∈ st.roots)
    (hp : p = r ∨ CanonBelow r p) : p ∉ st.files := by
  intro hk
  have hrf : RootForm r := (hw.roots.2 r hr).1
  by_cases hino : IsInoKey p
  · rcases hp with rfl | hc
    · exact nul_not_mem_root hrf hino
    · exact nul_not_mem_canonBelow hrf hc hino
  · apply hw.legacy p hk hino r hr
    rcases hp with rfl | hc
    · exact .inl rfl
    · exact isUnder_of_canonBelow hc

theorem NsWf.child_not_files (hw : NsWf st) {d b : GoString} (hd : st.ns !! d = some .dir)
    (hb : NameOk b) : child d b ∉ st.files := by
  obtain ⟨r, hr, hdr⟩ := hw.dir_form hd
  exact hw.not_files hr (.inr (canonBelow_child hdr hb))

theorem NsWf.dir_not_files (hw : NsWf st) {d : GoString} (hd : st.ns !! d = some .dir) :
    d ∉ st.files := by
  obtain ⟨r, hr, hdr⟩ := hw.dir_form hd
  exact hw.not_files hr hdr

theorem parentDir_child {d b : GoString} (hd : st.ns !! d = some .dir) (hb : NameOk b) :
    st.ParentDir (child d b) := ⟨d, parentOf_child' d b hb, hd⟩

end current

/-! ## A directory's changes -/

/-- `g` with the change `o` made. -/
def DirG.push (g : DirG) (o : LOp) : DirG := ⟨g.dur, g.pend ++ [o]⟩

theorem DirG.push_now (g : DirG) (o : LOp) : (g.push o).now = o.apply g.now :=
  lreplay_snoc _ _ _

theorem DirG.crashTo_now (g : DirG) : g.CrashTo g.now :=
  ⟨g.pend.length, Nat.le_refl _, by rw [List.take_length]; rfl⟩

theorem DirG.crashTo_push {g : DirG} {e : Ents} (o : LOp) (h : g.CrashTo e) :
    (g.push o).CrashTo e := by
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨i, by simp [DirG.push]; omega, ?_⟩
  simp only [DirG.push]
  rw [List.take_append_of_le_length hi]

theorem DirG.crashTo_push_now (g : DirG) (o : LOp) : (g.push o).CrashTo (o.apply g.now) := by
  refine ⟨(g.pend ++ [o]).length, by simp [DirG.push], ?_⟩
  simp only [DirG.push, List.take_length]
  exact (lreplay_snoc _ _ _).symm

/-! ## The directories an operation changes -/

theorem mem_toList_parentOf {p e : GoString} : e ∈ (parentOf p).toList ↔ parentOf p = some e := by
  cases parentOf p <;> simp [Option.toList, eq_comm]

theorem NsOp.touched_nil {o : NsOp} {e : GoString} (h : e ∉ o.dirs) : o.touched e = [] := by
  cases o with
  | create p k => simp only [NsOp.dirs, mem_toList_parentOf] at h; simp [NsOp.touched, h]
  | mkdir p => simp only [NsOp.dirs, mem_toList_parentOf] at h; simp [NsOp.touched, h]
  | remove p => simp only [NsOp.dirs, mem_toList_parentOf] at h; simp [NsOp.touched, h]
  | rename s t =>
    simp only [NsOp.dirs, List.mem_append, mem_toList_parentOf, not_or] at h
    simp [NsOp.touched, h.1, h.2]

theorem NsOp.adds_nil {o : NsOp} {e : GoString} (h : e ∉ o.dirs) : o.adds e = [] := by
  cases o with
  | create p k => simp only [NsOp.dirs, mem_toList_parentOf] at h; simp [NsOp.adds, h]
  | mkdir p => simp only [NsOp.dirs, mem_toList_parentOf] at h; simp [NsOp.adds, h]
  | remove p => simp [NsOp.adds]
  | rename s t =>
    simp only [NsOp.dirs, List.mem_append, mem_toList_parentOf, not_or] at h
    simp [NsOp.adds, h.2]

theorem OsDirFd.note_of_not_dirs {o : NsOp} (df : OsDirFd) (h : df.path ∉ o.dirs) :
    df.note o = df := by
  unfold OsDirFd.note
  split
  · rename_i u s r hrd
    rw [NsOp.touched_nil h, NsOp.adds_nil h]
    cases df; simp only at hrd; subst hrd
    simp
  · rfl

/-! ## What a file operation of a directory does to it -/

/-- The effect of a file operation `o` of the directory `d` on the namespace `m`: the change
`lo` of `d`'s entries, no other directory's entries changed, and the directories the same. -/
structure FileOpIn (m : NsMap) (d : GoString) (o : NsOp) (lo : LOp) : Prop where
  dirs : ∀ e, e ∈ o.dirs ↔ e = d
  self : entsOf (o.apply m) d = lo.apply (entsOf m d)
  other : ∀ e, e ≠ d → entsOf (o.apply m) e = entsOf m e
  dir : ∀ e, (o.apply m !! e = some .dir) ↔ (m !! e = some .dir)

theorem fileOpIn_create {m : NsMap} {d b k : GoString} (hb : NameOk b)
    (hn : m !! child d b = none) :
    FileOpIn m d (.create (child d b) k) (.put b (.file k)) := by
  refine ⟨?_, ?_, fun e he => ?_, fun e => ?_⟩
  · intro e; simp [NsOp.dirs, parentOf_child' d b hb, Option.toList, eq_comm]
  · exact entsOf_insert_child m d b _ hb
  · exact entsOf_insert_other m e _ _ (by rw [parentOf_child' d b hb]; simpa using he.symm)
  · show (<[child d b := OsNode.file k]> m) !! e = _ ↔ _
    by_cases he : child d b = e
    · subst he; rw [GMap.lookup_insert, hn]; simp
    · rw [GMap.lookup_insert_ne _ _ he]

theorem fileOpIn_remove {m : NsMap} {d b k : GoString} (hb : NameOk b)
    (hf : m !! child d b = some (.file k)) :
    FileOpIn m d (.remove (child d b)) (.del b) := by
  refine ⟨?_, ?_, fun e he => ?_, fun e => ?_⟩
  · intro e; simp [NsOp.dirs, parentOf_child' d b hb, Option.toList, eq_comm]
  · exact entsOf_delete_child m d b
  · exact entsOf_delete_other m e _ (by rw [parentOf_child' d b hb]; simpa using he.symm)
  · show (GMap.delete (child d b) m) !! e = _ ↔ _
    by_cases he : child d b = e
    · subst he; rw [GMap.lookup_delete, hf]; simp
    · rw [GMap.lookup_delete_ne _ he]

theorem fileOpIn_rename {m : NsMap} {d bs bt k : GoString} (hbs : NameOk bs) (hbt : NameOk bt)
    (hne : bs ≠ bt) (hf : m !! child d bs = some (.file k))
    (ht : m !! child d bt ≠ some .dir) :
    FileOpIn m d (.rename (child d bs) (child d bt)) (.mv bs bt) := by
  have happ : (NsOp.rename (child d bs) (child d bt)).apply m =
      <[child d bt := .file k]> (GMap.delete (child d bs) m) := by
    simp only [NsOp.apply, hf]
  refine ⟨?_, ?_, fun e he => ?_, fun e => ?_⟩
  · intro e; simp [NsOp.dirs, parentOf_child' d bs hbs, parentOf_child' d bt hbt, Option.toList, eq_comm]
  · rw [happ, entsOf_insert_child _ d bt _ hbt, entsOf_delete_child]
    have : entsOf m d !! bs = some (.file k) := by rw [entsOf_child m d bs hbs]; exact hf
    show _ = (match entsOf m d !! bs with
      | some n => <[bt := n]> (GMap.delete bs (entsOf m d))
      | none => entsOf m d)
    rw [this]
  · have hpe : ∀ b, NameOk b → parentOf (child d b) ≠ some e := fun b hb => by
      rw [parentOf_child' d b hb]; simpa using he.symm
    rw [happ, entsOf_insert_other _ e _ _ (hpe bt hbt), entsOf_delete_other _ e _ (hpe bs hbs)]
  · rw [happ]
    show (<[child d bt := OsNode.file k]> (GMap.delete (child d bs) m)) !! e = _ ↔ _
    by_cases h1 : child d bt = e
    · subst h1; rw [GMap.lookup_insert]
      constructor
      · intro h; cases h
      · intro h; exact absurd h ht
    · rw [GMap.lookup_insert_ne _ _ h1]
      by_cases h2 : child d bs = e
      · subst h2; rw [GMap.lookup_delete, hf]; simp
      · rw [GMap.lookup_delete_ne _ h2]

theorem OsDirFd.note_path (o : NsOp) (df : OsDirFd) : (df.note o).path = df.path := by
  unfold OsDirFd.note; split <;> rfl

/-! ## The coherence a file operation keeps -/

section coh
variable {st st1 : OsState} {V : NsMap × List NsOp} {Γdf : GMap w64 (GoString × DirPh)}

/-- The namespace now is the history replayed. -/
theorem ns_eq_replay (hw : NsWf st) (hc : NsCoh st V Γdf) : st.ns = nsReplay V.2 V.1 := by
  obtain ⟨h1, h2, h3⟩ := hc.hist
  generalize V.2.length - st.nsLog.length = c at h2 h3
  rw [hw.replay, h3, ← h2, ← nsReplay_append, List.take_append_drop]

/-- **An operation logged by the holder of the whole history** (so that no read is in
progress): the state after it is coherent with the history it extends. `st1` is the state the
operation is made from (the in-flight flag cleared, a file created), with `st`'s durable part, log
and directory fds. -/
theorem nsCoh_log {o : NsOp} (hc : NsCoh st V Γdf)
    (hnr : ∀ fd d rs g q, Γdf !! fd ≠ some (d, .reading rs g q))
    (h2 : st1.nsDur = st.nsDur) (h3 : st1.nsLog = st.nsLog) (h4 : st1.dfds = st.dfds) :
    NsCoh (st1.nsDo o) (V.1, V.2 ++ [o]) Γdf := by
  obtain ⟨⟨k1, k2, k3⟩, hfds, hph, -⟩ := hc
  have hl : (st1.nsDo o).nsLog = st.nsLog ++ [o] := by rw [← h3]; rfl
  have hc' : (V.2 ++ [o]).length - (st.nsLog ++ [o]).length = V.2.length - st.nsLog.length := by
    simp
  refine ⟨⟨?_, ?_, ?_⟩, fun fd => ?_, fun fd x df hx hdf => ?_, fun fd e rs g' q hx => ?_⟩
  · rw [hl]; simp; (try omega)
  · rw [hl, hc', List.drop_append_of_le_length (by omega), k2]
  · rw [hl, hc', List.take_append_of_le_length (by omega)]
    show st1.nsDur = _; rw [h2]; exact k3
  · show (Γdf !! fd).map (·.1) = ((GMap.fmap (·.note o) st1.dfds) !! fd).map (·.path)
    rw [GMap.lookup_fmap, h4, hfds fd]
    cases st.dfds !! fd with
    | none => rfl
    | some df => show some df.path = some (df.note o).path; rw [OsDirFd.note_path]
  · show PhOk x.2 df.rd
    have hdf' : (GMap.fmap (·.note o) st1.dfds) !! fd = some df := hdf
    rw [GMap.lookup_fmap, h4] at hdf'
    cases hd0 : st.dfds !! fd with
    | none => rw [hd0] at hdf'; cases hdf'
    | some df0 =>
      rw [hd0] at hdf'; simp only [Option.map_some, Option.some.injEq] at hdf'
      subst hdf'
      have hph0 := hph fd x df0 hx hd0
      rcases x with ⟨xp, _ | ⟨rs, g0, q⟩ | _⟩
      · unfold OsDirFd.note; split <;> simp_all [PhOk]
      · exact absurd hx (hnr fd xp rs g0 q)
      · unfold OsDirFd.note; split <;> simp_all [PhOk]
  · exact absurd hx (hnr fd e rs g' q)

/-- A commit of the first `n` operations of the log keeps the coherence (the history is the same;
more of it is committed). -/
theorem nsCoh_commit (hc : NsCoh st V Γdf) (n : Nat) : NsCoh (st.nsCommit n) V Γdf := by
  obtain ⟨⟨k1, k2, k3⟩, hfds, hph, hrd⟩ := hc
  generalize hcd : V.2.length - st.nsLog.length = c at k2 k3
  have hcl : c + st.nsLog.length = V.2.length := by omega
  have hl : (st.nsCommit n).nsLog = st.nsLog.drop n := rfl
  have hd : (st.nsCommit n).nsDur = nsReplay (st.nsLog.take n) st.nsDur := rfl
  by_cases hn : n ≤ st.nsLog.length
  · have hc' : V.2.length - (st.nsLog.drop n).length = c + n := by simp; omega
    refine ⟨⟨?_, ?_, ?_⟩, hfds, hph, hrd⟩
    · rw [hl]; simp; omega
    · rw [hl, hc', ← List.drop_drop, k2]
    · rw [hl, hd, hc', List.take_add, k2, k3, nsReplay_append]
  · have hn' : st.nsLog.length ≤ n := by omega
    have hc' : V.2.length - (st.nsLog.drop n).length = V.2.length := by simp [hn']
    refine ⟨⟨?_, ?_, ?_⟩, hfds, hph, hrd⟩
    · rw [hl]; simp; omega
    · rw [hl, hc', List.drop_eq_nil_of_le (Nat.le_refl _), List.drop_eq_nil_of_le hn']
    · rw [hl, hd, hc', List.take_of_length_le (Nat.le_refl _), List.take_of_length_le hn', k3,
        ← nsReplay_append, ← k2, List.take_append_drop]

end coh

/-! ## The shape a file operation keeps -/

section shape
variable {R : List GoString} {m : NsMap}

theorem shape_create {d b k : GoString} (hs : NsShape R m) (hd : m !! d = some .dir)
    (hdf : ∃ r ∈ R, d = r ∨ CanonBelow r d) (hb : NameOk b) (hn : m !! child d b = none)
    (hk : ∀ q, m !! q ≠ some (.file k)) : NsShape R (<[child d b := .file k]> m) := by
  obtain ⟨hR, hP, hL⟩ := hs
  have hne : ∀ q, m !! q = some .dir → child d b ≠ q := fun q hq h => by subst h; rw [hn] at hq; cases hq
  refine ⟨fun r hr => ?_, fun p x hp => ?_, fun p q k' hp hq => ?_⟩
  · rw [GMap.lookup_insert_ne _ _ (hne r (hR r hr))]; exact hR r hr
  · by_cases hpc : child d b = p
    · subst hpc
      obtain ⟨r, hr, hdr⟩ := hdf
      refine .inr ⟨⟨r, hr, canonBelow_child hdr hb⟩, d, parentOf_child' d b hb, ?_⟩
      rw [GMap.lookup_insert_ne _ _ (hne d hd)]; exact hd
    · rw [GMap.lookup_insert_ne _ _ hpc] at hp
      rcases hP p x hp with h | ⟨hc, dd, hdd, hddir⟩
      · exact .inl h
      · exact .inr ⟨hc, dd, hdd, by rw [GMap.lookup_insert_ne _ _ (hne dd hddir)]; exact hddir⟩
  · by_cases hpc : child d b = p <;> by_cases hqc : child d b = q
    · subst hpc; exact hqc
    · subst hpc; rw [GMap.lookup_insert] at hp; cases hp
      rw [GMap.lookup_insert_ne _ _ hqc] at hq; exact absurd hq (hk q)
    · subst hqc; rw [GMap.lookup_insert] at hq; cases hq
      rw [GMap.lookup_insert_ne _ _ hpc] at hp; exact absurd hp (hk p)
    · rw [GMap.lookup_insert_ne _ _ hpc] at hp; rw [GMap.lookup_insert_ne _ _ hqc] at hq
      exact hL p q k' hp hq

theorem shape_remove {p k : GoString} (hs : NsShape R m) (hf : m !! p = some (.file k)) :
    NsShape R (GMap.delete p m) := by
  obtain ⟨hR, hP, hL⟩ := hs
  have hne : ∀ q, m !! q = some .dir → p ≠ q := fun q hq h => by subst h; rw [hf] at hq; cases hq
  refine ⟨fun r hr => ?_, fun p' x hp' => ?_, fun p1 q1 k' hp1 hq1 => ?_⟩
  · rw [GMap.lookup_delete_ne _ (hne r (hR r hr))]; exact hR r hr
  · by_cases hpp : p = p'
    · subst hpp; rw [GMap.lookup_delete] at hp'; cases hp'
    · rw [GMap.lookup_delete_ne _ hpp] at hp'
      rcases hP p' x hp' with h | ⟨hc, dd, hdd, hddir⟩
      · exact .inl h
      · exact .inr ⟨hc, dd, hdd, by rw [GMap.lookup_delete_ne _ (hne dd hddir)]; exact hddir⟩
  · by_cases h1 : p = p1
    · subst h1; rw [GMap.lookup_delete] at hp1; cases hp1
    · by_cases h2 : p = q1
      · subst h2; rw [GMap.lookup_delete] at hq1; cases hq1
      · rw [GMap.lookup_delete_ne _ h1] at hp1; rw [GMap.lookup_delete_ne _ h2] at hq1
        exact hL p1 q1 k' hp1 hq1

theorem shape_rename {d s bt k : GoString} (hs : NsShape R m) (hd : m !! d = some .dir)
    (hdf : ∃ r ∈ R, d = r ∨ CanonBelow r d) (hbt : NameOk bt) (hf : m !! s = some (.file k))
    (ht : m !! child d bt ≠ some .dir) (hne : s ≠ child d bt) :
    NsShape R (<[child d bt := .file k]> (GMap.delete s m)) := by
  obtain ⟨hR, hP, hL⟩ := hs
  have hneT : ∀ q, m !! q = some .dir → child d bt ≠ q := fun q hq h => by subst h; exact ht hq
  have hneS : ∀ q, m !! q = some .dir → s ≠ q := fun q hq h => by subst h; rw [hf] at hq; cases hq
  have hlook : ∀ q, m !! q = some .dir →
      (<[child d bt := OsNode.file k]> (GMap.delete s m)) !! q = some .dir := fun q hq => by
    rw [GMap.lookup_insert_ne _ _ (hneT q hq), GMap.lookup_delete_ne _ (hneS q hq)]; exact hq
  refine ⟨fun r hr => hlook r (hR r hr), fun p x hp => ?_, fun p q k' hp hq => ?_⟩
  · by_cases hpt : child d bt = p
    · subst hpt
      obtain ⟨r, hr, hdr⟩ := hdf
      exact .inr ⟨⟨r, hr, canonBelow_child hdr hbt⟩, d, parentOf_child' d bt hbt, hlook d hd⟩
    · rw [GMap.lookup_insert_ne _ _ hpt] at hp
      by_cases hps : s = p
      · subst hps; rw [GMap.lookup_delete] at hp; cases hp
      · rw [GMap.lookup_delete_ne _ hps] at hp
        rcases hP p x hp with h | ⟨hc, dd, hdd, hddir⟩
        · exact .inl h
        · exact .inr ⟨hc, dd, hdd, hlook dd hddir⟩
  · have hget : ∀ p k', (<[child d bt := OsNode.file k]> (GMap.delete s m)) !! p = some (.file k') →
        (p = child d bt ∧ k' = k) ∨ (p ≠ child d bt ∧ p ≠ s ∧ m !! p = some (.file k')) := by
      intro p k' hp
      by_cases hpt : child d bt = p
      · subst hpt; rw [GMap.lookup_insert] at hp; cases hp; exact .inl ⟨rfl, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ hpt] at hp
        by_cases hps : s = p
        · subst hps; rw [GMap.lookup_delete] at hp; cases hp
        · rw [GMap.lookup_delete_ne _ hps] at hp
          exact .inr ⟨Ne.symm hpt, Ne.symm hps, hp⟩
    rcases hget p k' hp with ⟨rfl, rfl⟩ | ⟨hp1, hp2, hp3⟩ <;>
      rcases hget q k' hq with ⟨rfl, hk⟩ | ⟨hq1, hq2, hq3⟩
    · rfl
    · exact absurd (hL q s _ hq3 hf) hq2
    · subst hk; exact absurd (hL p s _ hp3 hf) hp2
    · exact hL p q k' hp3 hq3

end shape

/-! ## The well-formedness a file operation keeps -/

theorem nsWf_fileOp {st st1 : OsState} {o : NsOp} (hw : NsWf st)
    (h1 : st1.ns = st.ns) (h2 : st1.nsDur = st.nsDur) (h3 : st1.nsLog = st.nsLog)
    (h4 : st1.dfds = st.dfds) (hr : st1.roots = st.roots) (hfds : st1.fds = st.fds)
    (hfiles : ∀ k f, st.files !! k = some (some f) → ∃ f', st1.files !! k = some (some f'))
    (hdom : ∀ k, k ∈ st1.files → k ∈ st.files ∨ IsInoKey k)
    (hshape : NsShape st.roots (o.apply st.ns))
    (hkeys : ∀ p k, o.apply st.ns !! p = some (.file k) →
      IsInoKey k ∧ ∃ f, st1.files !! k = some (some f))
    (hdir : ∀ e, (o.apply st.ns !! e = some .dir) ↔ (st.ns !! e = some .dir)) :
    NsWf (st1.nsDo o) := by
  have hlog : (st1.nsDo o).nsLog = st.nsLog ++ [o] := by
    show st1.nsLog ++ [o] = _; rw [h3]
  have hns : (st1.nsDo o).ns = o.apply st.ns := by show o.apply st1.ns = _; rw [h1]
  have hdur : (st1.nsDo o).nsDur = st.nsDur := h2
  have hroots : (st1.nsDo o).roots = st.roots := hr
  refine ⟨hroots ▸ hw.roots, ?_, fun n hn => ?_, fun k hk hni r hr' => ?_, fun fd df hdf => ?_,
    fun fd hfd => ?_⟩
  · rw [hns, hlog, hdur, nsReplay_snoc, ← hw.replay]
  · rw [hlog] at hn ⊢; rw [hdur, hroots]
    simp only [List.length_append, List.length_singleton] at hn
    by_cases hle : n ≤ st.nsLog.length
    · rw [List.take_append_of_le_length hle]
      obtain ⟨hs, hk⟩ := hw.hist n hle
      refine ⟨hs, fun p k hp => ?_⟩
      obtain ⟨hino, f, hf⟩ := hk p k hp
      exact ⟨hino, hfiles k f hf⟩
    · rw [List.take_of_length_le (by simp; omega), nsReplay_snoc, ← hw.replay]
      exact ⟨hshape, hkeys⟩
  · rw [hroots] at hr'
    rcases hdom k hk with h | h
    · exact hw.legacy k h hni r hr'
    · exact absurd h hni
  · have hdf' : (GMap.fmap (·.note o) st1.dfds) !! fd = some df := hdf
    rw [GMap.lookup_fmap, h4] at hdf'
    cases hd0 : st.dfds !! fd with
    | none => rw [hd0] at hdf'; cases hdf'
    | some df0 =>
      rw [hd0] at hdf'; simp only [Option.map_some, Option.some.injEq] at hdf'
      subst hdf'
      rw [hns, OsDirFd.note_path, hdir]; exact hw.dfds fd df0 hd0
  · have : (st1.nsDo o).dfds !! fd = (GMap.fmap (·.note o) st1.dfds) !! fd := rfl
    rw [this, GMap.lookup_fmap, h4, hw.disj fd (by rwa [← hfds])]; rfl

end Perennial

end
