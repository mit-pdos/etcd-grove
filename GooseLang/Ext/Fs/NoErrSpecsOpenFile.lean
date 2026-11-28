/-
What the program logic may use of the premises **no I/O error** (`NoIoErr`) and **no error of the
lock, mapping and descriptor calls** (`NoMapLockErr`, pending the user's review) on `open(2)` of a
covered path in the shared mode (session S3d): a failing step of `open` with `O_CREAT`, without
`O_TRUNC`, of a name holding a file or nothing (`wp_osOpenCreateSQ`), or of a name holding a file
(`wp_osOpenFileSQ`), fails only with `EINTR` (`open_failure_eintr`): with a free fd the semantics has
a success there, which `NoIoErr` then asks for; with none, `NoMapLockErr` asks for `EINTR`.
The shared-mode specs with that errno (`wp_osOpenCreateSNE`, `wp_osOpenFileSNE`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoMapLockErr
public import GooseLang.Ext.Fs.TreeSharedCreate
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]
variable {tf : GoTypeFns}

/-- **A failing `open` of a covered path fails with `EINTR`** when its call has a success from every
free fd (`hsucc`): with a free fd, `NoIoErr` asks for errno 0; with none, `NoMapLockErr` for `EINTR`
(its outcome `isFsStep_open_eintr`). -/
theorem open_failure_eintr {Sio : IoSet} [hio : FsStepSat (NoIoErr Sio)]
    [hml : FsStepSat (NoMapLockErr Sio)] {k : Nat} {p : GoString} {fl : w64} (hS : Sio.path p ∧ PathFits p)
    {h : GMap Loc (NonAtomic val)} {st : OsState} {e' : Expr} {h' : GMap Loc (NonAtomic val)}
    {st' : OsState}
    (hsucc : ∀ fd, FdFree st fd →
      ∃ st'', IsFsStep "Open" (PairV (osTokV k) (PairV (#p) (#fl))) st (osRes (#fd) 0) st'')
    (hst : IsFsStep "Open" (PairV (osTokV k) (PairV (#p) (#fl))) st e' st')
    (hs : S.step tf "Open" (PairV (osTokV k) (PairV (#p) (#fl))) h st () e' h' st' ()) :
    ∀ fd e : w64, e' = osRes (#fd) e → e ≠ 0 → e = EINTR := by
  intro fd e he hne
  subst he
  have hzero : ∀ r : val, osRes (#fd) e ≠ osRes r 0 := by
    intro r hr
    injection hr with hr
    injection hr with _ hr
    exact hne (go.intoVal_inj hr)
  by_cases hf : ∃ fd', FdFree st fd'
  · obtain ⟨fd', hfd'⟩ := hf
    obtain ⟨st'', hs''⟩ := hsucc fd' hfd'
    obtain ⟨r, hr⟩ := (hio.sat _ _ _ _ _ _ _ _ _ hs ⟨k, p, fl, rfl, hS.1, hS.2⟩).1
      ⟨_, st'', hs'', ⟨_, rfl⟩⟩
    exact absurd hr (hzero r)
  · have hc : MapLockCovers Sio "Open" (PairV (osTokV k) (PairV (#p) (#fl))) st :=
      ⟨⟨k, p, fl, rfl, hS.1⟩, fun fd' h => hf ⟨fd', h⟩⟩
    obtain ⟨st'', hs'', -⟩ := isFsStep_open_eintr hst
    rcases hml.sat _ _ _ _ _ _ _ _ _ hs hc ⟨_, st'', hs'', Or.inr rfl⟩ with ⟨r, hr⟩ | hr
    · exact absurd hr (hzero r)
    · injection hr with hr
      injection hr with _ hr
      exact go.intoVal_inj hr

/-- **`open(O_CREAT)` of `d/b` has a success from every free fd**, without `O_TRUNC` or with the name
absent: the name holds a file (opened) or nothing (created), `d` a directory. -/
theorem openCreate_succ {st : OsState} {d b : GoString} {j : Ino} {k s0 : Nat} {fl : w64}
    (hfl : OpenFlagsOk fl.toNat) (hcr : fl.toNat / O_CREAT % 2 = 1)
    (htr : fl.toNat / O_TRUNC % 2 = 0 ∨ st.tree.entry j b = none)
    (hw : FsTreeWf st) (hcall : st.proc.calls !! k = some (s0, child d b)) (hp : st.lookup d = some (.dir j))
    (hb : NameOk b) (hnd : ∀ J, st.tree.entry j b ≠ some (.dir J)) :
    ∀ fd, FdFree st fd →
      ∃ st'', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st (osRes (#fd) 0) st'' := by
  intro fd hfree
  have hl : (st.metaEnd k).lookup (child d b) = st.tree.entry j b := lookup_child hw.roots hp hb
  have hpar : (st.metaEnd k).parent (child d b) = some (j, b) := parent_child hp hb
  have hcr' : decide ((fl.toNat / O_CREAT) % 2 = 1) = true := by simp [hcr]
  cases hen : st.tree.entry j b with
  | none =>
    let st0 := st.metaEnd k
    refine ⟨_, .inl ⟨child d b, fl, k, s0, rfl, .inr (treeName_child hp hb), hfl, hcall,
      ⟨(fun _ i' hi' => by
        have hi2 : (st.metaEnd k).lookup (child d b) = some (.file i') := hi'
        rw [hl, hen] at hi2; cases hi2),
      .inl ⟨((st0.setFile st0.fs.nextIno newFile).takeIno).metaDo (.create j b st0.fs.nextIno) s0,
        .file st.fs.nextIno, fd, ?_, hfree, rfl, rfl⟩⟩⟩⟩
    unfold OpenEffect
    rw [hl, hen]
    exact ⟨hcr', j, b, hpar, rfl, rfl⟩
  | some n =>
    cases n with
    | dir J => exact absurd hen (hnd J)
    | file i =>
      have htr0 : fl.toNat / O_TRUNC % 2 = 0 := htr.resolve_right (by rw [hen]; nofun)
      have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr0]
      obtain ⟨f, hf⟩ := file_of_entry hw hen
      refine ⟨_, .inl ⟨child d b, fl, k, s0, rfl, .inr (treeName_child hp hb), hfl, hcall,
        fun h => absurd h (by simp [htr']), .inl ⟨st.metaEnd k, .file i, fd, ?_, hfree, rfl, rfl⟩⟩⟩
      unfold OpenEffect
      rw [hl, hen]
      refine ⟨⟨f, hf, ?_⟩, rfl⟩
      simp only [htr', Bool.false_eq_true, ↓reduceIte]

/-- **`open(2)` without `O_TRUNC` of `d/b`, holding the file `i`, has a success from every free fd.** -/
theorem openFile_succ {st : OsState} {d b : GoString} {i : Ino} {k s0 : Nat} {fl : w64}
    (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 0)
    (hw : FsTreeWf st) (hcall : st.proc.calls !! k = some (s0, child d b))
    (hl : st.lookup (child d b) = some (.file i)) :
    ∀ fd, FdFree st fd →
      ∃ st'', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st (osRes (#fd) 0) st'' := by
  intro fd hfree
  have hl0 : (st.metaEnd k).lookup (child d b) = some (.file i) := hl
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
  have hfile : ∃ f, st.file i = some f := by
    have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
    rw [List.take_length] at this
    exact this i (named_of_lookup hl)
  obtain ⟨f, hf⟩ := hfile
  refine ⟨_, .inl ⟨child d b, fl, k, s0, rfl, treePath_of_lookup hl, hfl, hcall,
    fun h => absurd h (by simp [htr']), .inl ⟨st.metaEnd k, .file i, fd, ?_, hfree, rfl, rfl⟩⟩⟩
  unfold OpenEffect
  rw [hl0]
  refine ⟨⟨f, hf, ?_⟩, rfl⟩
  simp only [htr', Bool.false_eq_true, ↓reduceIte]

/-- **`open(2)` with `O_TRUNC` of `d/b`, holding the file `i` not busy, has a success from every free fd.** -/
theorem openTrunc_succ {st : OsState} {d b : GoString} {i : Ino} {k s0 : Nat} {fl : w64}
    (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 1)
    (hw : FsTreeWf st) (hcall : st.proc.calls !! k = some (s0, child d b))
    (hl : st.lookup (child d b) = some (.file i)) (hnb : ¬ BusyAt (st.metaEnd k) i) :
    ∀ fd, FdFree st fd →
      ∃ st'', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st (osRes (#fd) 0) st'' := by
  intro fd hfree
  have hl0 : (st.metaEnd k).lookup (child d b) = some (.file i) := hl
  have hfile : ∃ f, st.file i = some f := by
    have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
    rw [List.take_length] at this
    exact this i (named_of_lookup hl)
  obtain ⟨f, hf⟩ := hfile
  refine ⟨_, .inl ⟨child d b, fl, k, s0, rfl, treePath_of_lookup hl, hfl, hcall,
    ⟨(fun _ i' hi' => by
      have hi2 : (st.metaEnd k).lookup (child d b) = some (.file i') := hi'
      rw [hl0] at hi2; cases hi2; exact hnb),
    .inl ⟨if decide (fl.toNat / O_TRUNC % 2 = 1) = true then
        (st.metaEnd k).stampFile i (fun n => let c := OsChange.ofResize i f 0 true;
          (f.announce c n).land c c.hi 0)
      else st.metaEnd k, .file i, fd, ?_, hfree, rfl, rfl⟩⟩⟩⟩
  unfold OpenEffect
  rw [hl0]
  exact ⟨⟨f, hf, rfl⟩, rfl⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [S : ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`open(2)` with `O_CREAT`, without `O_TRUNC`, of `d/b` with no error** (shared mode, the claim
whole; `d/b` covered): `wp_osOpenCreateS'`, a failure's errno `EINTR`. -/
theorem wp_osOpenCreateSNE (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]
    (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat) (hcr : fl.toNat / O_CREAT % 2 = 1)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hs : h.next ≤ s0) (hS : Sio.path (child d b) ∧ PathFits (child d b)) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ fd : w64, ∀ e : w64, ⌜e ≠ 0 → e = EINTR⌝ -∗ osCallPerm (L := L) (callKey R d) q -∗
        osPathS (L := L) R d dq j -∗
        ((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜h.cur !! b = none⌝ ∗ ∃ x i, osLogged (L := L) x (⟨.create j b i, s0⟩ : LogEntry) ∗
            osNames (L := L) j (.only [b]) (DFrac.own 1) (h.log x (⟨.create j b i, s0⟩ : LogEntry) (<[b := .file i]> h.cur)) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h)) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} :=
  wp_osOpenCreateSQ R d b j dq h k s0 q fl hfl hcr (.inl htr) hb hnd hs hE hE' Φ (· = EINTR)
    (fun st _e' _st' hw hcall hp hent Hst Hsem => by
      obtain ⟨hh, hh', Hsem⟩ := Hsem
      exact open_failure_eintr hS
        (openCreate_succ hfl hcr (.inl htr) hw hcall hp hb (fun J => by rw [hent]; exact hnd J)) Hst Hsem)

/-- **`open(2)` of `d/b`, holding the file `i`, without `O_TRUNC`, with no error** (shared mode;
`d/b` covered): `wp_osOpenFileS'`, a failure's errno `EINTR`. -/
theorem wp_osOpenFileSNE (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]
    (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) (hS : Sio.path (child d b) ∧ PathFits (child d b)) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1 ∧ e = EINTR)⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} :=
  wp_osOpenFileSQ R d b j i N dq dqn h k s0 q fl hfl htr hb hN hi hE hE' Φ (· = EINTR)
    (fun st _e' _st' hw hcall hl Hst Hsem => by
      obtain ⟨hh, hh', Hsem⟩ := Hsem
      exact open_failure_eintr hS (openFile_succ hfl htr hw hcall hl) Hst Hsem)

/-- **`open(2)` of `d/b`, holding the file `i`, without `O_TRUNC`, its error witnessed** (shared mode,
`wp_osOpenFileS`, wal-fsfix2): an errno other than `EINTR` (which the models retry) only when the file
system can fail on `d/b` or the path does not fit (the witness
`¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b))`). -/
theorem wp_osOpenFileSW (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        ⌜e ≠ 0 → e = EINTR ∨ ¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b))⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  iintro #Hos #Hsi Hp Hn Hk HΦ
  by_cases hW : FsNoErrOn (· = child d b) ∧ PathFits (child d b)
  · obtain ⟨⟨Sio, -, h1, h2, hp⟩, hf⟩ := hW
    haveI := h1; haveI := h2
    iapply wp_osOpenFileSNE Sio R d b j i N dq dqn h k s0 q fl hfl htr hb hN hi ⟨hp _ rfl, hf⟩ hE hE' Φ
      $$ Hos Hsi Hp Hn Hk
    iintro %fd %e %hres Hperm Hp Hn Hfd
    iapply HΦ $$ %fd %e [] [] Hperm Hp Hn Hfd
    · ipureintro; rcases hres with h0 | ⟨h1, h2, -⟩; exact .inl h0; exact .inr ⟨h1, h2⟩
    · ipureintro; intro hne; rcases hres with ⟨h0, -⟩ | ⟨-, -, h3⟩; exact absurd h0 hne; exact .inl h3
  · iapply wp_osOpenFileS' R d b j i N dq dqn h k s0 q fl hfl htr hb hN hi hE hE' Φ $$ Hos Hsi Hp Hn Hk
    iintro %fd %e %hres Hperm Hp Hn Hfd
    iapply HΦ $$ %fd %e %hres [] Hperm Hp Hn Hfd
    ipureintro; exact fun _ => .inr hW

end specs

end Fs
end Perennial

end
