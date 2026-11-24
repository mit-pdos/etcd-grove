/-
The definitions and lemmas of `openWALFiles.lean`'s proof (`walOpenedRc`, `walRcLink`, `walOpen_triple`, ...),
in a module of their own so that `openLastHeld.lean` imports them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.closeAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile
public import Spec.fmt.ErrorfErrsTerm
public import Spec.errors.IsPathErrnoTerm
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader
public import Spec.path.filepath.Join
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas

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
  iprop(∃ (f : Loc) (fd : w64) (rl : Loc) (lo lk : Option Bool),
    os.ownFile f fd (child dir b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (walSegFd write lo lk i) ∗
    fdLocksW fd (walSegFd write lo lk i) ∗ os.ownOff f (W64 0) ∗ ⌜0 ≤ fd.toInt⌝ ∗
    ⌜GoInterface.ok fr = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl⌝ ∗
    rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ∗
    (if write then fileutil.lockedFile lf f ∗
        ⌜rc = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf⌝
      else ⌜lf = null ∧ rc = interface.mkOk (go.GoType.PointerType os.File.ty) #f⌝))

theorem walOpenedRc_file (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc)
    (rc : GoInterface) :
    walOpenedRc (GF := GF) write dir b i fr lf rc ⊢ walOpenedFile write dir b i fr lf := by
  unfold walOpenedRc walOpenedFile
  iintro ⟨%f, %fd, %rl, %lo, %lk, Hf, Hfd, Hlks, Ho, %h0, %hfr, #Hrl, Hw⟩
  iexists f, fd, rl, lo, lk
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
    (rc : GoInterface) (hb : os.closeErrMax (child dir b) ≤ wal.closeMsgMax) :
    walOpenedRc (GF := GF) write dir b i fr lf rc ⊢ wal.rcFile rc := by
  unfold walOpenedRc wal.rcFile
  iintro ⟨%f, %fd, %rl, %lo, %lk, Hf, Hfd, Hlks, -, -, -, -, Hw⟩
  ihave Hlks := fdLocksW_locks _ _ $$ Hlks
  iexists f, fd, child dir b, _
  iframe
  isplitr
  swap
  · ipureintro; exact hb
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
    (hl : rcs.length = j) (hj : j ≤ is.length)
    (hns : ∀ m, os.closeErrMax (child dir (ns.getD m [])) ≤ wal.closeMsgMax) :
    walOpenedRcs (GF := GF) write dir ns is j frs lfs rcs ⊢ [∗list] rc ∈ rcs, wal.rcFile rc := by
  unfold walOpenedRcs
  refine (BigSepL.bigSepL_mono (fun {m x} _ =>
    walOpenedRc_rcFile (GF := GF) write dir _ x _ _ _ (hns m))).trans ?_
  exact rcFiles_take is j rcs hl hj

/-- What the closer keeps of a file `openWALFiles` opened (persistent): the reader's `*fileReader` over
the `*os.File` `f`, and the `io.ReadCloser` collected (`rc`): the lock (write mode) or the file. -/
def walRcLink (write : Bool) (fr : GoInterfaceOk) (lf : Loc) (rc : GoInterface) : IProp GF :=
  iprop(∃ (f rl : Loc),
    ⌜GoInterface.ok fr = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl⌝ ∗
    rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ∗
    (if write then fileutil.lockedFile lf f ∗
        ⌜rc = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf⌝
      else ⌜rc = interface.mkOk (go.GoType.PointerType os.File.ty) #f⌝))

instance walRcLink_persistent (write : Bool) (fr : GoInterfaceOk) (lf : Loc) (rc : GoInterface) :
    Persistent (walRcLink (GF := GF) write fr lf rc) := by
  unfold walRcLink; cases write <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

theorem walOpenedRc_split (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc)
    (rc : GoInterface) :
    walOpenedRc (GF := GF) write dir b i fr lf rc ⊢
      walOpenedFile write dir b i fr lf ∗ walRcLink write fr lf rc := by
  iintro H
  ihave #Hl : walRcLink (GF := GF) write fr lf rc $$ [H]
  · iunfold walOpenedRc at H
    icases H with ⟨%f, %fd, %rl, %lo, %lk, -, -, -, -, -, %hfr, #Hrl, Hw⟩
    iunfold walRcLink
    iexists f, rl
    isplitr
    · ipureintro; exact hfr
    iframe Hrl
    cases write
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hw with %hw
      ipureintro; exact hw.2
    · simp only [↓reduceIte]
      iexact Hw
  · iframe Hl
    iapply walOpenedRc_file
    iexact H

theorem walOpenedRcs_split (write : Bool) (dir : GoString) (ns : List GoString) (is : List Ino) (j : Nat)
    (frs : List GoInterfaceOk) (lfs : List Loc) (rcs : List GoInterface) :
    walOpenedRcs (GF := GF) write dir ns is j frs lfs rcs ⊢
      ([∗list] m ↦ i ∈ is.take j, walOpenedFile write dir (ns.getD m []) i
        (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩) (lfs.getD m null)) ∗
      [∗list] m ↦ _i ∈ is.take j, walRcLink write (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩)
        (lfs.getD m null) (rcs.getD m GoInterface.nil) := by
  unfold walOpenedRcs
  refine (BigSepL.bigSepL_mono (fun {m x} _ => walOpenedRc_split (GF := GF) write dir _ x _ _ _)).trans ?_
  exact BigSepL.bigSepL_sep_eqv.1

/-- The closer's step: a file closable again, with what the closer kept of it, is `closeAll`'s. -/
theorem walRcLink_rcFile (write : Bool) (fr : GoInterfaceOk) (lf : Loc) (rc : GoInterface) :
    walRcLink (GF := GF) write fr lf rc ∗ wal.walClosable write fr lf ⊢ wal.rcFile rc := by
  iintro ⟨#Hl, Hc⟩
  iunfold walRcLink at Hl
  iunfold wal.walClosable at Hc
  icases Hl with ⟨%f, %rl, %hfr, #Hrl, #Hw⟩
  icases Hc with ⟨%f', %rl', %fd, %nm, %fl, %hfr', #Hrl', Hf, Hfd, Hlks, -, %hnm⟩
  have hrl : rl' = rl := by
    have h1 := hfr'.symm.trans hfr
    unfold interface.mkOk at h1
    injection h1 with h1
    injection h1 with h2 h3
    exact go.intoVal_inj h3
  subst hrl
  icombine Hrl Hrl' gives %he
  have hf : f' = f := by
    injection he with he
    exact he.symm
  subst hf
  iunfold wal.rcFile
  iexists f', fd, nm, fl
  iframe Hf Hfd Hlks
  isplitr
  swap
  · ipureintro; exact hnm
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hw with %hw
    ileft; ipureintro; exact hw
  · simp only [↓reduceIte]
    icases Hw with ⟨#Hlk, %hw⟩
    iright
    iexists lf
    iframe Hlk
    ipureintro; exact hw

/-- `[∗list]` over two lists of the same length, of a predicate of the index only. -/
theorem bigSepL_idx_congr {A B : Type} (Φ : Nat → IProp GF) :
    ∀ (l1 : List A) (l2 : List B), l1.length = l2.length →
    ([∗list] k ↦ _x ∈ l1, Φ k) ⊢ [∗list] k ↦ _y ∈ l2, Φ k
  | [], [], _ => .rfl
  | _ :: l1, _ :: l2, h => by
    refine (BigSepL.bigSepL_cons (Φ := fun k (_ : A) => Φ k)).1.trans
      ((sep_mono .rfl ?_).trans (BigSepL.bigSepL_cons (Φ := fun k (_ : B) => Φ k)).2)
    exact bigSepL_idx_congr (fun k => Φ (k + 1)) l1 l2 (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A `[∗list]` over `l` is one over its indices, each element `l.getD m d`. -/
theorem bigSepL_getD_self {A : Type} (Φ : Nat → A → IProp GF) (l : List A) (d : A) :
    ([∗list] m ↦ x ∈ l, Φ m x) ⊢ [∗list] m ↦ _x ∈ l, Φ m (l.getD m d) := by
  apply BigSepL.bigSepL_mono
  intro m x hm
  rw [List.getD_eq_getElem?_getD, hm, Option.getD_some]

theorem bigSepL_getD_self_r {A : Type} (Φ : Nat → A → IProp GF) (l : List A) (d : A) :
    ([∗list] m ↦ _x ∈ l, Φ m (l.getD m d)) ⊢ [∗list] m ↦ x ∈ l, Φ m x := by
  apply BigSepL.bigSepL_mono
  intro m x hm
  rw [List.getD_eq_getElem?_getD, hm, Option.getD_some]

/-- **The closer's precondition gives `closeAll`'s**, with what the closer kept of each file. -/
theorem walClose_rcFiles (write : Bool) (is : List Ino) (j : Nat) (frs : List GoInterfaceOk)
    (lfs : List Loc) (rcs : List GoInterface) (hf : frs.length = j) (hr : rcs.length = j)
    (hj : j ≤ is.length) :
    ([∗list] m ↦ _i ∈ is.take j, walRcLink (GF := GF) write (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩)
        (lfs.getD m null) (rcs.getD m GoInterface.nil)) ∗
      ([∗list] m ↦ fr ∈ frs, wal.walClosable write fr (lfs.getD m null)) ⊢
      [∗list] rc ∈ rcs, wal.rcFile rc := by
  have htl : (is.take j).length = j := by simp; omega
  iintro ⟨Hl, Hc⟩
  ihave Hc2 := bigSepL_getD_self (GF := GF) (fun m fr => wal.walClosable write fr (lfs.getD m null)) frs
    ⟨go.GoType.PointerType go.string, #()⟩ $$ Hc
  ihave Hc3 := bigSepL_idx_congr (GF := GF) (fun m => wal.walClosable write
    (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩) (lfs.getD m null)) frs (is.take j)
    (by rw [hf, htl]) $$ Hc2
  ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [Hl Hc3]
  · iframe
  ihave H2 := BigSepL.bigSepL_mono (fun {m x} _ => (sep_comm.1.trans
    (walRcLink_rcFile (GF := GF) write _ _ (rcs.getD m GoInterface.nil)))) $$ H
  ihave H3 := bigSepL_idx_congr (GF := GF) (fun m => wal.rcFile (rcs.getD m GoInterface.nil)) (is.take j) rcs
    (by rw [hr, htl]) $$ H2
  iapply (bigSepL_getD_self_r (GF := GF) (fun _ rc => wal.rcFile rc) rcs GoInterface.nil)
  iexact H3

theorem walOpen_getElem? {α : Type} (l : List α) (n : Nat) (h : n < l.length) :
    ∃ b, l[n]? = some b := ⟨_, List.getElem?_eq_getElem h⟩

theorem walOpen_lt_sub (jj k len : w64) (hk0 : 0 ≤ sint.Z k) (hkz : sint.Z k ≤ sint.Z len)
    (hj0 : 0 ≤ sint.Z jj) (h : sint.nat jj < sint.nat len - sint.nat k) :
    sint.Z jj < sint.Z (len - k) := by
  have e1 : sint.Z (len - k) = sint.Z len - sint.Z k := by word
  rw [e1]; simp only [sint.nat, sint.Z] at *; omega

theorem walOpen_eq_sub (jj k len : w64) (hk0 : 0 ≤ sint.Z k) (hkz : sint.Z k ≤ sint.Z len)
    (hj0 : 0 ≤ sint.Z jj) (hle : sint.nat jj ≤ sint.nat len - sint.nat k)
    (h : ¬ sint.Z jj < sint.Z (len - k)) :
    sint.nat jj = sint.nat len - sint.nat k := by
  have e1 : sint.Z (len - k) = sint.Z len - sint.Z k := by word
  rw [e1] at h; simp only [sint.nat, sint.Z] at *; omega

theorem walOpen_succ (jj : w64) (n : Nat) (hj0 : 0 ≤ sint.Z jj) (hn : n < 2 ^ 63)
    (h : sint.nat jj < n) : sint.nat (jj + W64 1) = sint.nat jj + 1 := by word

/-- A `fmtErrorOk` error is `errOk` (as `fileutil.errOk_of_fmtErrorOk`, a proof file's lemma). -/
theorem walOpen_errOk (e : GoInterfaceOk) :
    fmtErrorOkOrNil (GF := GF) (GoInterface.ok e) ⊢ errOk e := by
  exact errOk_of_fmtErrorOkOrNil e

/-- `os.OpenFile(d/b, flag, 0600)` of a file `b` of a claim, as `TryLockFile` takes it: the
claim's resources lent and given back, the inode `i`. -/
theorem walOpen_triple [os.Assumptions] [os.file.FieldAssumptions] (R : Roots) (d b : GoString) (dq : DFrac) (j i : Ino)
    (N : NameSet) (dqn : DFrac) (h : NamesH) (qc : Qp) (flag : w64)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    fileutil.OpenTriple (X := Unit)
      (iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc))
      (child d b) flag (W32 384)
      (fun _ _ => iprop(osPathS (GF := GF) R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc))
      (fun _ i' => i' = i) := by
  unfold fileutil.OpenTriple
  iintro %Φ ⟨#Hospkg, #Hinv, #Hsi, Hp, Hn, Hperm⟩ HΦ
  wp_apply os.OpenFile.wp_fileS d b flag (W32 384) R j i N dq dqn h qc hfl htr hb hN hi
    $$ [Hp Hn Hperm] as %f %err ⟨Hp, Hn, Hperm, Hr⟩
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iunfold fileutil.openPost
  iexists ()
  icases Hr with (⟨%fd, %hh, Hf, Ho, Hfd⟩ | ⟨%hh, Herr, -⟩)
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

/-- `walOpen_triple`, a failed open witnessed (wal-fsfix2): the file system can fail on `d/b`, or the
path does not fit (`os.OpenFile.wp_fileS`'s error arm). -/
theorem walOpen_tripleW [os.Assumptions] [os.file.FieldAssumptions] (R : Roots) (d b : GoString) (dq : DFrac) (j i : Ino)
    (N : NameSet) (dqn : DFrac) (h : NamesH) (qc : Qp) (flag : w64)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    fileutil.OpenTriple (X := Unit)
      (iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc))
      (child d b) flag (W32 384)
      (fun _ ok => iprop(osPathS (GF := GF) R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ⌜ok = false → ¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b))⌝))
      (fun _ i' => i' = i) := by
  unfold fileutil.OpenTriple
  iintro %Φ ⟨#Hospkg, #Hinv, #Hsi, Hp, Hn, Hperm⟩ HΦ
  wp_apply os.OpenFile.wp_fileS d b flag (W32 384) R j i N dq dqn h qc hfl htr hb hN hi
    $$ [Hp Hn Hperm] as %f %err ⟨Hp, Hn, Hperm, Hr⟩
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iunfold fileutil.openPost
  iexists ()
  icases Hr with (⟨%fd, %hh, Hf, Ho, Hfd⟩ | ⟨%hh, Herr, %ee, -, -, %hW⟩)
  · ileft
    isplitr
    · ipureintro; exact hh.1
    simp only []
    iframe
    isplitr
    · ipureintro; nofun
    ipureintro; exact ⟨hh.2, rfl⟩
  · iright
    isplitr
    · ipureintro; exact hh
    simp only []
    iframe
    ipureintro; exact fun _ => hW

end proof

end EtcdGrove
end Perennial
