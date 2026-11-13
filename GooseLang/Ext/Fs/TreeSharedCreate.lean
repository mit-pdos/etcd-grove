/-
The shared mode of the tree: `open(2)` with `O_RDWR | O_CREAT` of a name of a claim
(`wp_osOpenCreateS`), over `wp_logStepSW`: the file there opened, or a new one created (its `create`
logged, its `OsMeta` and perhaps an fd minted in the files' world). `TreeShared.lean` states the spec
and takes its proof from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedMeta

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Pure facts -/

theorem tokPathFl_inj [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {k k' : Nat}
    {p p' : GoString} {f f' : w64}
    (h : PairV (osTokV k') (PairV (#p') (#f')) = PairV (osTokV k) (PairV (#p) (#f))) :
    k' = k ∧ p' = p ∧ f' = f := by
  injection h with h1 h2
  injection h2 with h3 h4
  refine ⟨?_, go.intoVal_inj h3, go.intoVal_inj h4⟩
  injection h1 with h1; exact extVal_inj h1

theorem files_next_none {st : OsState} (hw : FsTreeWf st) : st.fs.files !! st.fs.nextIno = none := by
  cases h0 : st.fs.files !! st.fs.nextIno with
  | none => rfl
  | some f => exact absurd (hw.files_lt _ (by rw [GMap.mem_iff, h0]; rfl)) (Nat.lt_irrefl _)

theorem file_of_entry {st : OsState} (hw : FsTreeWf st) {j : Ino} {b : GoString} {i : Ino}
    (he : st.tree.entry j b = some (.file i)) : ∃ f, st.file i = some f := by
  have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
  rw [List.take_length] at this
  exact this i ⟨j, b, he⟩

/-- The fd `fd` added: still well formed, where no directory fd is `fd`. -/
theorem fsTreeWf_addFd {X : OsState} (hw : FsTreeWf X) {fd : w64} {d : OsFd}
    (hfd : X.proc.dfds !! fd = none) :
    FsTreeWf (X.setProc { X.proc with fds := <[fd := d]> X.proc.fds }) := by
  refine ⟨hw.roots, hw.hist, hw.dfds, fun fd' h' => ?_, hw.files_lt⟩
  show X.proc.dfds !! fd' = none
  by_cases he : fd = fd'
  · subst he; exact hfd
  · apply hw.disj fd'
    have h'' : (<[fd := d]> X.proc.fds) !! fd' ≠ none := h'
    rwa [GMap.lookup_insert_ne _ _ he] at h''

/-- **The state after a create is well formed** (any directory fds: they only note the create). -/
theorem fsTreeWf_created {st : OsState} (hw : FsTreeWf st) (k : Nat) {j : Ino} {b : GoString}
    (s0 : Nat) (hj : Reach st.fs.roots st.tree j) (hb : NameOk b) (he : st.tree.entry j b = none) :
    FsTreeWf (createdSt st k j b s0) := by
  have hnf := files_next_none hw
  have hnn : ¬ Named st.tree st.fs.nextIno := by
    intro hnm
    have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
    rw [List.take_length] at this
    obtain ⟨f, hf⟩ := this _ hnm
    rw [hnf] at hf; cases hf
  have hjm : j ∈ st.tree := (treeWf_now hw).1 j hj
  have htw := treeWf_create (treeWf_now hw) hj hb he hnn
  have hfilesC : ∀ i, (createdSt st k j b s0).fs.files !! i =
      if st.fs.nextIno = i then some newFile else st.fs.files !! i := fun i => files_setFile _ _ _ _
  refine fsTreeWf_meta hw rfl rfl rfl (fun i f hf => ?_) (Nat.le_succ _) htw (fun i hi => ?_)
    (fun j' hj' => ?_) (fun fd df h => ?_) (fun fd h => ?_) (fun i hi => ?_)
  · rw [hfilesC]; split
    · exact ⟨_, rfl⟩
    · exact ⟨f, hf⟩
  · rw [hfilesC]; split
    · exact ⟨_, rfl⟩
    · rename_i hni
      obtain ⟨j0, b0, hb0⟩ := hi
      simp only [MetaOp.apply] at hb0
      rw [entry_upd] at hb0
      split at hb0
      · rename_i hjj; subst hjj
        rw [GMap.lookup_insert_eq_iff] at hb0; split at hb0
        · cases hb0; exact absurd rfl hni
        · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
          rw [List.take_length] at this
          exact this i ⟨_, b0, by unfold Tree.entry; rw [← getD_lookup]; exact hb0⟩
      · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
        rw [List.take_length] at this
        exact this i ⟨j0, b0, hb0⟩
  · simp only [MetaOp.apply] at hj'
    rw [mem_upd] at hj'
    show j' < st.fs.nextIno + 1
    rcases hj' with rfl | hj'
    · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.2 _ (by
        rw [List.take_length]; exact hjm)
      exact Nat.lt_succ_of_lt this
    · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.2 j' (by
        rw [List.take_length]; exact hj')
      exact Nat.lt_succ_of_lt this
  · have h' : (GMap.fmap (·.note (.create j b st.fs.nextIno)) st.proc.dfds) !! fd = some df := h
    rw [GMap.lookup_fmap] at h'
    cases hd : st.proc.dfds !! fd with
    | none => rw [hd] at h'; simp at h'
    | some df0 =>
      rw [hd] at h'; simp only [Option.map_some, Option.some.injEq] at h'
      subst h'; rw [note_ino]; exact hw.dfds fd df0 hd
  · show (GMap.fmap (·.note (.create j b st.fs.nextIno)) st.proc.dfds) !! fd = none
    rw [GMap.lookup_fmap, hw.disj fd h]; rfl
  · show i < st.fs.nextIno + 1
    have hi' : (<[st.fs.nextIno := newFile]> st.fs.files) !! i ≠ none := by
      have hi2 : i ∈ (<[st.fs.nextIno := newFile]> st.fs.files) := hi
      rw [GMap.mem_iff] at hi2; intro h0; rw [h0] at hi2; cases hi2
    rw [GMap.lookup_insert_eq_iff] at hi'; split at hi'
    · rename_i hni; subst hni; exact Nat.lt_succ_self _
    · have := hw.files_lt i (by rw [GMap.mem_iff]; cases h0 : st.fs.files !! i with
        | none => exact absurd h0 hi'
        | some _ => rfl)
      exact Nat.lt_succ_of_lt this

theorem createdSt_dfds_none {st : OsState} {k : Nat} {j : Ino} {b : GoString} {s0 : Nat} {fd : w64}
    (h : st.proc.dfds !! fd = none) : (createdSt st k j b s0).proc.dfds !! fd = none := by
  show (GMap.fmap (·.note (.create j b st.fs.nextIno)) st.proc.dfds) !! fd = none
  rw [GMap.lookup_fmap, h]; rfl

theorem not_loggedT_same {st st' : OsState} {k s0 : Nat} {o : MetaOp} (h : LoggedT st st' k s0 o)
    (hl : st'.fs.metaLog = st.fs.metaLog) : False := by
  have := congrArg List.length (h.log.symm.trans hl); simp at this

theorem not_endedT_snoc {st st' : OsState} {k : Nat} (h : EndedT st st' k) {e : LogEntry}
    (hl : st'.fs.metaLog = st.fs.metaLog ++ [e]) : False := by
  have := congrArg List.length (h.log.symm.trans hl); simp at this

/-- **The outcomes of `open(2)` with `O_CREAT`, without `O_TRUNC`, of `d/b`** (`d` the directory `j`, `b` no
directory): a failure with no effect; the file there opened; a new file created, with or
without its fd. -/
theorem openCreateStep_cases [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {st : OsState}
    {d b : GoString} {j : Ino} {k s0 : Nat} {fl : w64} {e' : Expr} {st' : OsState}
    (hcr : fl.toNat / O_CREAT % 2 = 1) (htr : fl.toNat / O_TRUNC % 2 = 0) (hw : FsTreeWf st)
    (hcall : st.proc.calls !! k = some s0) (hp : st.lookup d = some (.dir j)) (hb : NameOk b)
    (hnd : ∀ J, st.tree.entry j b ≠ some (.dir J))
    (Hst : IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st') :
    (∃ e : w64, e ≠ 0 ∧ e' = osRes (#(-1 : w64)) e ∧ st' = st.metaEnd k) ∨
    (∃ i fd, st.tree.entry j b = some (.file i) ∧ FdFree st fd ∧ e' = osRes (#fd) 0 ∧
      st' = (st.metaEnd k).setProc { (st.metaEnd k).proc with
        fds := <[fd := openFd i fl]> (st.metaEnd k).proc.fds }) ∨
    (st.tree.entry j b = none ∧ ∃ e : w64, e ≠ 0 ∧ e' = osRes (#(-1 : w64)) e ∧
      st' = createdSt st k j b s0) ∨
    (st.tree.entry j b = none ∧ ∃ fd, FdFree st fd ∧ e' = osRes (#fd) 0 ∧
      st' = (createdSt st k j b s0).setProc { (createdSt st k j b s0).proc with
        fds := <[fd := openFd st.fs.nextIno fl]> (createdSt st k j b s0).proc.fds }) := by
  simp only [IsFsStep] at Hst
  obtain ⟨p', fl', k', s', hv, -, -, hk', hres⟩ := Hst
  obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
  rw [hcall] at hk'; cases hk'
  have hcr' : decide ((fl.toNat / O_CREAT) % 2 = 1) = true := by simp [hcr]
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
  simp only [hcr', htr'] at hres
  obtain ⟨-, hres⟩ := hres
  have hl : (st.metaEnd k).lookup (child d b) = st.tree.entry j b := lookup_child hw.roots hp hb
  have hpar : (st.metaEnd k).parent (child d b) = some (j, b) := parent_child hp hb
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl] at heff
    cases hen : st.tree.entry j b with
    | none =>
      rw [hen] at heff
      obtain ⟨-, j', b', hp', rfl, rfl⟩ := heff
      rw [hpar] at hp'; cases hp'
      right; right; right
      refine ⟨rfl, fd, hfree, rfl, ?_⟩
      rw [hst]; rfl
    | some n =>
      rw [hen] at heff
      cases n with
      | dir J => exact absurd hen (hnd J)
      | file i =>
        obtain ⟨⟨f, -, h1⟩, rfl⟩ := heff
        simp only [Bool.false_eq_true, ↓reduceIte] at h1
        subst h1
        right; left
        refine ⟨i, fd, rfl, hfree, rfl, ?_⟩
        rw [hst]; rfl
  · rcases hst with rfl | ⟨tgt, heff⟩
    · left; exact ⟨e, he, rfl, rfl⟩
    · unfold OpenEffect at heff
      rw [hl] at heff
      cases hen : st.tree.entry j b with
      | none =>
        rw [hen] at heff
        obtain ⟨-, j', b', hp', rfl, rfl⟩ := heff
        rw [hpar] at hp'; cases hp'
        right; right; left
        exact ⟨rfl, e, he, rfl, rfl⟩
      | some n =>
        rw [hen] at heff
        cases n with
        | dir J => exact absurd hen (hnd J)
        | file i =>
          obtain ⟨⟨f, -, h1⟩, -⟩ := heff
          simp only [Bool.false_eq_true, ↓reduceIte] at h1
          left; exact ⟨e, he, rfl, h1⟩

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The files' world after a create** (no fd yet), the heap as it was: the new file's `OsMeta`. -/
theorem osWorld_created {st : OsState} {Γb Γm Γf Γt} {h : GMap Loc (NonAtomic val)}
    (hw : FsTreeWf st) (k : Nat) (j : Ino) (b : GoString) (s0 : Nat) :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗
      osWorld (L := L) (createdSt st k j b s0) Γb (<[st.fs.nextIno := newMeta]> Γm) Γf Γt h ∗
      osMeta (L := L) st.fs.nextIno (DFrac.own 1) newMeta := by
  unfold osWorld
  iintro ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  have hnf := files_next_none hw
  have hfn0 : (st.metaEnd k).file st.fs.nextIno = none := hnf
  have hs0 := filesSame_metaEnd st k
  have hwf0 := osWf_filesSame hs0 hwf
  have hcoh0 := osCoh_filesSame hs0 hcoh
  have hsA := filesSame_created st k j b s0
  have hΓm : Γm !! st.fs.nextIno = none := (hcoh.meta_dom _).2 hnf
  imod gAuth_insert _ _ _ st.fs.nextIno newMeta hΓm $$ HAm with ⟨HAm, Hm⟩
  have hcv : cellView (createdSt st k j b s0) = cellView st := by
    rw [cellView_filesSame hsA (osWf_create hwf0 hfn0), cellView_create hwf0 hfn0]
    exact cellView_filesSame hs0 hwf
  imodintro
  rw [hcv]
  unfold osMeta
  iframe
  ipureintro
  exact ⟨osWf_filesSame hsA (osWf_create hwf0 hfn0),
    osCoh_filesSame hsA (osCoh_create hwf0 hcoh0 hfn0)⟩

/-- What an `open(O_CREAT)` gives of a file `i`: a failure, or an fd. -/
def ocFd (fl fd e : w64) (i : Ino) : IProp GF :=
  iprop(⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))

/-- What an `open(O_CREAT)` of `b` (the claim's entries `cur`) gives of the files' world: a created
file `n` (logged), its `OsMeta` and perhaps an fd; or (not logged) the file there and perhaps an fd,
or a failure. -/
def ocGift (fl : w64) (cur : Ents) (b : GoString) (n : Nat) (w : val) (lg : Bool) : IProp GF :=
  iprop(∃ fd e : w64, ⌜w = PairV (#fd) (#e)⌝ ∗
    ((⌜lg = true⌝ ∗ osMeta (L := L) n (DFrac.own 1) newMeta ∗ ocFd (L := L) fl fd e n) ∨
     (⌜lg = false⌝ ∗ ((∃ i, ⌜cur !! b = some (.file i)⌝ ∗ ocFd (L := L) fl fd e i) ∨
       ⌜e ≠ 0 ∧ fd = -1⌝))))

theorem wp_osOpenCreateS' (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat) (hcr : fl.toNat / O_CREAT % 2 = 1)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hs : h.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        ((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜h.cur !! b = none⌝ ∗ ∃ x i, osLogged (L := L) x (⟨.create j b i, s0⟩ : LogEntry) ∗
            osNames (L := L) j (.only [b]) (DFrac.own 1) (h.log x (⟨.create j b i, s0⟩ : LogEntry) (<[b := .file i]> h.cur)) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h)) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hbN' : ∀ b', (NameSet.only [b]).Mem b' → b' = b := by simp [NameSet.Mem]
  let oF : Nat → MetaOp := fun n => .create j b n
  let cl : List ClaimW := [(j, .only [b], h, ∅)]
  let curF : Nat → ClaimW → Ents := fun n _ => <[b := .file n]> h.cur
  let W : val → Bool → Prop := fun w lg =>
    ∃ fd e : w64, w = PairV (#fd) (#e) ∧ (lg = true → h.cur !! b = none)
  have hentE : ∀ st, ClaimsAt st cl → st.tree.entry j b = h.cur !! b := fun st hat =>
    hat.ent _ (List.mem_singleton_self _) b hbN
  have hndE : ∀ st, ClaimsAt st cl → ∀ J, st.tree.entry j b ≠ some (.dir J) := by
    intro st hat J; rw [hentE st hat]; exact hnd J
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' ∧
        FilesSame st st' := by
    intro st _ _ hcall _ hp _
    have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
    exact ⟨_, st.metaEnd k, ⟨child d b, fl, k, s0, rfl, .inr (treeName_child hp hb), hfl,
      hcall, ⟨fun h => (Bool.false_ne_true (htr'.symm.trans h)).elim,
        .inr ⟨1, by decide, rfl, .inl rfl⟩⟩⟩, filesSame_metaEnd st k⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      ∃ w, e' = Val w ∧ FsTreeWf st' ∧
        ((EndedT st st' k ∧ W w false) ∨ (LoggedT st st' k s0 (oF st.fs.nextIno) ∧ W w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    rcases openCreateStep_cases hcr htr hw hcall hp hb (hndE st hat) Hst with
      ⟨e, -, rfl, rfl⟩ | ⟨i, fd, -, hfree, rfl, rfl⟩ | ⟨hen, e, -, rfl, rfl⟩ | ⟨hen, fd, hfree, rfl, rfl⟩
    · exact ⟨_, rfl, fsTreeWf_metaEnd hw k,
        .inl ⟨endedT_metaEnd st k, _, _, rfl, fun h => by cases h⟩⟩
    · exact ⟨_, rfl, fsTreeWf_addFd (fsTreeWf_metaEnd hw k) hfree.2.2,
        .inl ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, _, _, rfl, fun h => by cases h⟩⟩
    · exact ⟨_, rfl, fsTreeWf_created hw k s0 (reach_of_lookup hp) hb hen,
        .inr ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, _, _, rfl, fun _ => (hentE st hat).symm.trans hen⟩⟩
    · exact ⟨_, rfl, fsTreeWf_addFd (fsTreeWf_created hw k s0 (reach_of_lookup hp) hb hen)
          (createdSt_dfds_none hfree.2.2),
        .inr ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, _, _, rfl, fun _ => (hentE st hat).symm.trans hen⟩⟩
  have hworld : ∀ st e' st' (hh hh' : GMap Loc (NonAtomic val)) Γb Γm Γf Γt w lg, FsTreeWf st →
      st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      e' = Val w → W w lg → (lg = false → EndedT st st' k) →
      (lg = true → LoggedT st st' k s0 (oF st.fs.nextIno)) →
      HeapRendered st st' hh hh' → MapsFresh st st' hh →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt hh ==∗ ∃ Γb' Γm' Γf' Γt',
        osWorld (L := L) st' Γb' Γm' Γf' Γt' hh' ∗ ocGift (L := L) fl h.cur b st.fs.nextIno w lg := by
    intro st e' st' hh hh' Γb Γm Γf Γt w lg hw _ hcall _ hp hat Hst hew _ hend hlog Hr Hfr
    rcases openCreateStep_cases hcr htr hw hcall hp hb (hndE st hat) Hst with
      ⟨e, he, rfl, rfl⟩ | ⟨i, fd, hen, hfree, rfl, rfl⟩ | ⟨hen, e, he, rfl, rfl⟩ | ⟨hen, fd, hfree, rfl, rfl⟩
    · cases lg with
      | true => exact absurd (hlog rfl) (fun h' => not_loggedT_same h' rfl)
      | false =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_filesSame (filesSame_metaEnd st k) Hr Hfr $$ Hw with Hw
        imodintro
        iexists Γb, Γm, Γf, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists (-1 : w64), e
        isplitr
        · ipureintro; rfl
        iright; isplitr
        · ipureintro; rfl
        iright; ipureintro; exact ⟨he, rfl⟩
    · cases lg with
      | true => exact absurd (hlog rfl) (fun h' => not_loggedT_same h' rfl)
      | false =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_addFd (filesSame_metaEnd st k) (d := openFd i fl) hfree.2.1
          (file_of_entry hw hen) Hr Hfr $$ Hw with ⟨Hw, Hfd⟩
        imodintro
        iexists Γb, Γm, _, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists fd, (0 : w64)
        isplitr
        · ipureintro; rfl
        iright; isplitr
        · ipureintro; rfl
        ileft; iexists i
        isplitr
        · ipureintro; rw [← hentE st hat]; exact hen
        unfold ocFd
        iright
        isplitr
        · ipureintro; exact ⟨rfl, hfree.1⟩
        · iexact Hfd
    · cases lg with
      | false => exact absurd (hend rfl) (fun h' => not_endedT_snoc h' rfl)
      | true =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_created hw k j b s0 $$ Hw with ⟨Hw, Hm⟩
        imod osWorld_filesSame (filesSame_refl _) Hr Hfr $$ Hw with Hw
        imodintro
        iexists Γb, _, Γf, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists (-1 : w64), e
        isplitr
        · ipureintro; rfl
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hm]
        · iexact Hm
        unfold ocFd
        ileft; ipureintro; exact ⟨he, rfl⟩
    · cases lg with
      | false => exact absurd (hend rfl) (fun h' => not_endedT_snoc h' rfl)
      | true =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_created hw k j b s0 $$ Hw with ⟨Hw, Hm⟩
        imod osWorld_addFd (st := createdSt st k j b s0) (filesSame_refl _) (fd := fd)
          (d := openFd st.fs.nextIno fl) hfree.2.1 ⟨_, file_setFile_eq _ _ _⟩ Hr Hfr
          $$ Hw with ⟨Hw, Hfd⟩
        imodintro
        iexists Γb, _, _, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists fd, (0 : w64)
        isplitr
        · ipureintro; rfl
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hm]
        · iexact Hm
        unfold ocFd
        iright
        isplitr
        · ipureintro; exact ⟨rfl, hfree.1⟩
        · iexact Hfd
  have htree : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      LoggedT st st' k s0 (oF st.fs.nextIno) →
      let o := oF st.fs.nextIno
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) := by
    intro st e' st' hw _ hcall hp hat Hst hlf
    have hen : st.tree.entry j b = none := by
      rcases openCreateStep_cases hcr htr hw hcall hp hb (hndE st hat) Hst with
        ⟨_e, _he, _he', hst'⟩ | ⟨_i, _fd, _h1, _h2, _h3, hst'⟩ | ⟨hen, -⟩ | ⟨hen, -⟩
      · exact absurd hlf (fun h' => not_loggedT_same h' (by rw [hst']; rfl))
      · exact absurd hlf (fun h' => not_loggedT_same h' (by rw [hst']; rfl))
      · exact hen
      · exact hen
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm : j ∈ st.tree := mem_of_reach htw (reach_of_lookup hp)
    have hnf := files_next_none hw
    refine ⟨fun x hx => ?_, fun J hJ => by simp [oF, MetaOp.newDirs] at hJ,
      fun _ => ⟨⟨hjm, hen⟩, ?_⟩, fun c hc => ?_⟩
    · simp only [oF, MetaOp.apply] at hx
      rw [mem_upd] at hx
      rcases hx with rfl | hx
      · exact .inl hjm
      · exact .inl hx
    · intro j' b' i ho t ht hnm
      simp only [oF, MetaOp.create.injEq] at ho
      obtain ⟨-, -, rfl⟩ := ho
      obtain ⟨f, hf⟩ := (hw.hist t ht).2.1 _ hnm
      rw [hnf] at hf; cases hf
    · rw [List.mem_singleton] at hc; subst hc
      apply GMap.ext; intro b'
      show restrictN (.only [b]) (entsOf _ j) !! b' = (<[b := .file st.fs.nextIno]> h.cur) !! b'
      by_cases hb' : (NameSet.only [b]).Mem b'
      · obtain rfl := hbN' b' hb'
        rw [restrictN_lookup _ _ _ hb', entsOf_lookup, entry_create, if_pos ⟨rfl, rfl⟩,
          GMap.lookup_insert]
      · rw [restrictN_lookup_not _ _ _ hb']
        have hne : b ≠ b' := fun h => hb' (h ▸ hbN)
        rw [GMap.lookup_insert_ne _ _ hne]
        exact (hat.out _ (List.mem_singleton_self _) b' hb').symm
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepSW "Open" _ (by simp [val.isPanic]) R k s0 q oF cl curF
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j)) W (ocGift (L := L) fl h.cur b)
    (by simp [cl]) (fun _ c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨b, hbN, .inl (by simp [oF, MetaOp.slots])⟩)
    (by intro n sl hsl; simp [oF, MetaOp.slots] at hsl; subst hsl
        exact ⟨_, List.mem_singleton_self _, rfl, hbN⟩)
    (by simp [cl, hs]) (fun _ hd => hd.elim)
    (by intro n j' b' hb'; simp [oF, MetaOp.adds] at hb'; rw [hb'.2]; exact hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost hworld htree hE hE' Φ
    $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, ⟨%n, HG⟩, Hl⟩ | ⟨%hW, %n, %x, HG, Hlg, Hl, -⟩)
  · obtain ⟨fd, e, rfl, -⟩ := hW
    unfold ocGift
    icases HG with ⟨%fd', %e', %hfe, HG⟩
    injection hfe with h1 h2
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    icases HG with (⟨%hlg, -⟩ | ⟨-, HG⟩)
    · cases hlg
    iapply HΦ $$ %fd %e Hq Hp
    icases HG with (⟨%i, %hi, HG⟩ | %hf)
    · ileft
      iexists i
      isplitr
      · ipureintro; exact hi
      isplitl [Hl]
      · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
      unfold ocFd; iexact HG
    · iright; iright
      isplitr
      · ipureintro; exact hf
      iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨fd, e, rfl, hnone⟩ := hW
    unfold ocGift
    icases HG with ⟨%fd', %e', %hfe, HG⟩
    injection hfe with h1 h2
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    icases HG with (⟨-, Hm, HG⟩ | ⟨%hlg, -⟩)
    · iapply HΦ $$ %fd %e Hq Hp
      iright; ileft
      isplitr
      · ipureintro; exact hnone rfl
      iexists x, n
      isplitl [Hlg]
      · iexact Hlg
      isplitl [Hl]
      · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
      isplitl [Hm]
      · iexact Hm
      unfold ocFd; iexact HG
    · cases hlg

/-- **`open(2)` of `d/b`, a name holding the file `i`, without `O_TRUNC`** (shared mode), with a
fraction of a claim on names containing `b`: no entry; on success a fresh fd on `i`. -/
theorem wp_osOpenFileS' (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_fs_stepM "Open" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h0 Hw Ht
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
  icases osPathS_lookup hR hcoh.2 d dq j $$ HAn Hp with %hl
  icases osNames_entry hcoh.2 j N dqn h $$ HAn Hn with %hent
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  have hen : st.tree.entry j b = some (.file i) := by rw [hent b hN]; exact hi
  have hl' : st.lookup (child d b) = some (.file i) := by rw [lookup_child hw.roots hl hb]; exact hen
  have hl0 : (st.metaEnd k).lookup (child d b) = some (.file i) := hl'
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by
    have := hc.calls k; rw [hk] at this; exact this.symm
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h0 _ $$ Hσ Hcells with %Hag
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h0) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h0, _, ⟨child d b, fl, k, s0, rfl, treePath_of_lookup hl', hfl, hcall,
      ⟨fun h => absurd h (by simp [htr']), .inr ⟨1, by decide, rfl, .inl rfl⟩⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', fl', k', s', hv, -, -, hk', hres⟩ := Hst
  obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
  rw [hcall] at hk'; cases hk'
  simp only [htr', Bool.false_eq_true, ↓reduceIte] at hres
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h0 $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl0] at heff
    obtain ⟨⟨f', -, hst1⟩, rfl⟩ := heff
    simp only [htr', Bool.false_eq_true, ↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hst'' : st' = (st.metaEnd k).setProc { (st.metaEnd k).proc with
        fds := <[fd := openFd i fl]> (st.metaEnd k).proc.fds } := hst
    subst hst''
    imod osWorld_addFd (filesSame_metaEnd st k) (d := openFd i fl) hfdn (file_of_entry hw hen)
      Hr Hfr $$ Hw with ⟨Hw, Hfd⟩
    imodintro
    iexists Γb, Γm, <[fd := openFd i fl]> Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st)
          (st' := (st.metaEnd k).setProc { (st.metaEnd k).proc with
            fds := <[fd := openFd i fl]> (st.metaEnd k).proc.fds }) (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [OsState.metaEnd, OsState.setProc]
      try unfold treeShared
      iexists V0, s1, Γdf, GMap.delete k Γc
      iframe
      ipureintro
      exact ⟨fsTreeWf_addFd (fsTreeWf_metaEnd hw k) hdfn,
        (treeCohS_metaEnd hc k).congr rfl rfl rfl rfl⟩
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩) [Hq] Hp Hn
    · unfold osCallPerm; iexact Hq
    rw [if_pos rfl]; iexact Hfd
  · have hst' : st' = st.metaEnd k := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold OpenEffect at heff; rw [hl0] at heff
        obtain ⟨⟨f', -, h1⟩, -⟩ := heff
        simpa [htr'] using h1
    subst hst'
    imod osWorld_filesSame (filesSame_metaEnd st k) Hr Hfr $$ Hw with Hw
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
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) [Hq] Hp Hn
    · unfold osCallPerm; iexact Hq
    rw [if_neg he]; iempintro

end specs

end Fs
end Perennial

end
