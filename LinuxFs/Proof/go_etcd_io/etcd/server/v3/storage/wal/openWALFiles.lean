/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/openWALFiles.lean` (W5 of
`notes/wal-fsext-plan.md`; `sorry`: the callees `fileutil.TryLockFile`, `fileutil.NewFileReader`, `filepath.Join`, `closeAll` have no spec yet).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.closeAll
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Proof.os.NsS
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- A file `openWALFiles` opened, with the `io.ReadCloser` it collected (`rcs`): `walOpenedFile`'s
resources and `rc` the lock (write mode) or the file (read mode). -/
def walOpenedRc (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc)
    (rc : GoInterface) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (rl : Loc),
    os.ownFile f fd (child dir b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (openFd i (walReadFlag write)) ∗
    os.ownOff f (W64 0) ∗ ⌜0 ≤ fd.toInt⌝ ∗
    ⌜GoInterface.ok fr = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl⌝ ∗
    rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ∗
    (if write then fileutil.lockedFile lf f ∗
        ⌜rc = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf⌝
      else ⌜lf = null ∧ rc = interface.mkOk (go.GoType.PointerType os.File.ty) #f⌝))

theorem walOpenedRc_file (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc)
    (rc : GoInterface) :
    walOpenedRc (GF := GF) write dir b i fr lf rc ⊢ walOpenedFile write dir b i fr lf := by
  unfold walOpenedRc walOpenedFile
  iintro ⟨%f, %fd, %rl, Hf, Hfd, Ho, %h0, %hfr, #Hrl, Hw⟩
  iexists f, fd, rl
  iframe
  isplitr
  · ipureintro; exact h0
  isplitr
  · ipureintro; exact hfr
  isplitr
  · iexact Hrl
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hw with %hw
    ipureintro; exact hw.1
  · simp only [↓reduceIte]
    icases Hw with ⟨#Hl, -⟩
    iexact Hl

theorem walOpenedRc_rcFile (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc)
    (rc : GoInterface) :
    walOpenedRc (GF := GF) write dir b i fr lf rc ⊢ wal.rcFile rc := by
  unfold walOpenedRc wal.rcFile
  iintro ⟨%f, %fd, %rl, Hf, Hfd, -, -, -, -, Hw⟩
  iexists f, fd, child dir b, _
  iframe
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hw with %hw
    ileft
    ipureintro; exact hw.2
  · simp only [↓reduceIte]
    icases Hw with ⟨#Hl, %hrc⟩
    iright
    iexists lf
    iframe Hl
    ipureintro; exact hrc

/-- The opened files, by position: the `m`-th of `is.take j` with the `m`-th reader, lock and
closer. -/
def walOpenedRcs (write : Bool) (dir : GoString) (ns : List GoString) (is : List Ino) (j : Nat)
    (frs : List GoInterfaceOk) (lfs : List Loc) (rcs : List GoInterface) : IProp GF :=
  iprop([∗list] m ↦ i ∈ is.take j, walOpenedRc write dir (ns.getD m []) i
    (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩) (lfs.getD m null) (rcs.getD m GoInterface.nil))

theorem walOpenedRcs_snoc (write : Bool) (dir : GoString) (ns : List GoString) (is : List Ino)
    (j : Nat) (i : Ino) (frs : List GoInterfaceOk) (lfs : List Loc) (rcs : List GoInterface)
    (fr : GoInterfaceOk) (lf : Loc) (rc : GoInterface) (hi : is[j]? = some i)
    (hl : frs.length = j ∧ lfs.length = j ∧ rcs.length = j) :
    walOpenedRcs (GF := GF) write dir ns is j frs lfs rcs ∗
        walOpenedRc write dir (ns.getD j []) i fr lf rc ⊢
      walOpenedRcs write dir ns is (j + 1) (frs ++ [fr]) (lfs ++ [lf]) (rcs ++ [rc]) := by
  obtain ⟨h1, h2, h3⟩ := hl
  have hj : j < is.length := by
    rcases Nat.lt_or_ge j is.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  have htake : is.take (j + 1) = is.take j ++ [i] := by
    rw [List.take_succ, hi]; rfl
  have htl : (is.take j).length = j := by simp; omega
  unfold walOpenedRcs
  rw [htake]
  refine (sep_mono ?_ ?_).trans BigSepL.bigSepL_snoc.2
  · apply BigSepL.bigSepL_mono
    intro k x hk
    have hkj : k < j := by
      have := (List.getElem?_eq_some_iff.1 hk).1; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]
  · rw [htl]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    simp only [h1, h2, h3, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    exact .rfl

theorem rcFiles_take (is : List Ino) :
    ∀ (j : Nat) (rcs : List GoInterface), rcs.length = j → j ≤ is.length →
    ([∗list] m ↦ _i ∈ is.take j, wal.rcFile (GF := GF) (rcs.getD m GoInterface.nil)) ⊢
      [∗list] rc ∈ rcs, wal.rcFile rc
  | 0, rcs, hl, _ => by
    rw [List.length_eq_zero_iff.1 hl]
    simp only [List.take_zero, BigSepL.bigSepL_nil]
    exact .rfl
  | j + 1, rcs, hl, hj => by
    obtain ⟨rcs', r, rfl⟩ : ∃ rcs' r, rcs = rcs' ++ [r] := by
      rcases List.eq_nil_or_concat rcs with h | ⟨L, b, h⟩
      · subst h; simp at hl
      · exact ⟨L, b, by simpa using h⟩
    have hl' : rcs'.length = j := by simp at hl; omega
    have htake : is.take (j + 1) = is.take j ++ [is[j]'(by omega)] := by
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]; rfl
    rw [htake]
    refine BigSepL.bigSepL_snoc.1.trans ((sep_mono ?_ ?_).trans BigSepL.bigSepL_snoc.2)
    · refine (BigSepL.bigSepL_mono ?_).trans (rcFiles_take is j rcs' hl' (by omega))
      intro m x hm
      have hmj : m < j := by
        have := (List.getElem?_eq_some_iff.1 hm).1; simp at this; omega
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · have htl : (is.take j).length = j := by simp; omega
      rw [htl]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [hl', Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      exact .rfl

theorem walOpenedRcs_close (write : Bool) (dir : GoString) (ns : List GoString) (is : List Ino)
    (j : Nat) (frs : List GoInterfaceOk) (lfs : List Loc) (rcs : List GoInterface)
    (hl : rcs.length = j) (hj : j ≤ is.length) :
    walOpenedRcs (GF := GF) write dir ns is j frs lfs rcs ⊢ [∗list] rc ∈ rcs, wal.rcFile rc := by
  unfold walOpenedRcs
  refine (BigSepL.bigSepL_mono (fun {m x} _ => walOpenedRc_rcFile (GF := GF) write dir _ x _ _ _)).trans ?_
  exact rcFiles_take is j rcs hl hj

/-- `os.OpenFile(d/b, flag, 0600)` of a file `b` of a claim, as `TryLockFile` takes it: the
claim's resources lent and given back, the inode `i`. -/
theorem walOpen_triple [os.Assumptions] [os.file.FieldAssumptions] (R : Roots) (d b : GoString) (dq : DFrac) (j i : Ino)
    (N : NameSet) (dqn : DFrac) (h : NamesH) (qc : Qp) (flag : w64)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    fileutil.OpenTriple (X := Unit)
      (iprop(osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc))
      (child d b) flag (W32 384)
      (fun _ _ => iprop(osPathS (GF := GF) R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc))
      (fun _ i' => i' = i) := by
  unfold fileutil.OpenTriple
  iintro %Φ ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩ HΦ
  wp_apply os.OpenFile.wp_fileS d b flag (W32 384) R j i N dq dqn h qc hfl htr hb hN hi
    $$ [Hp Hn Hperm] as %f %err ⟨Hp, Hn, Hperm, Hr⟩
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iunfold fileutil.openPost
  iexists ()
  icases Hr with (⟨%fd, %hh, Hf, Ho, Hfd⟩ | ⟨%hh, Herr⟩)
  · ileft
    isplitr
    · ipureintro; exact hh.1
    simp only []
    iframe
    ipureintro; exact ⟨hh.2, rfl⟩
  · iright
    isplitr
    · ipureintro; exact hh
    simp only []
    iframe

theorem go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.wp_proof
    [os.Assumptions] [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (wp_TryLock : go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile.spec (GF := GF) (hG := hG))
    (wp_NewFileReader : go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_closeAll : go_etcd_io.etcd.server.v3.storage.wal.closeAll.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec (GF := GF) (hG := hG) := by
  intro lg d sl names dqs k write is R j dq qc N dqn h hk0 hkl hlen hd hnames
  wp_start as ⟨#Hlg, #Hinv, #Hsi, Hp, Hperm, Hn, Hsl⟩
  ihave %hclean := osPathS_cleanAbs R d dq j $$ Hp
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Hslw := ownSlice_wf _ _ _ $$ Hsl
  wp_auto
  wp_apply (wp_slice_make2 (V := GoInterface) (W64 0)) as %rc0 ⟨Hrc0, Hrcc0⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoInterface) (W64 0)) as %rs0 ⟨Hrs0, Hrsc0⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %ls0 ⟨Hls0, Hlsc0⟩
  · ipureintro; decide
  (try wp_auto)
  have hkz : sint.Z k ≤ sint.Z sl.len := by have := Hsll.1; word
  rw [if_pos ⟨hk0, hkz, Hslw.2⟩]
  icases (ownSlice_slice k sl.len sl dqs names ⟨hk0, hkz, Int.le_refl _⟩).1 $$ Hsl with ⟨Hw1, Hw2, Hw3⟩
  have hsub : subslice (sint.nat k) (sint.nat sl.len) names = names.drop (sint.nat k) := by
    rw [subslice_def, ← Hsll.1, List.take_length]
  rw [hsub]
  generalize hns : names.drop (sint.nat k) = ns at hlen hnames
  (try wp_auto)
  sorry

end proof

end EtcdGrove
end Perennial
