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
  ihave %Hw2l := ownSlice_len _ _ _ $$ Hw2
  ihave IH : iprop(∃ (jj : w64) (nv : GoString) (rcsl rssl lssl : GoSlice) (frs : List GoInterfaceOk)
      (lfs : List Loc) (rcs : List GoInterface),
      "i" ∷ i_ptr ↦ jj ∗ "name" ∷ name_ptr ↦ nv ∗
      "rcs" ∷ rcs_ptr ↦ rcsl ∗ "Hrc" ∷ rcsl ↦* rcs ∗ "Hrcc" ∷ ownSliceCap GoInterface rcsl (DFrac.own 1) ∗
      "rs" ∷ rs_ptr ↦ rssl ∗ "Hrs" ∷ rssl ↦* frs.map GoInterface.ok ∗
      "Hrsc" ∷ ownSliceCap GoInterface rssl (DFrac.own 1) ∗
      "ls" ∷ ls_ptr ↦ lssl ∗ "Hls" ∷ lssl ↦* lfs ∗ "Hlsc" ∷ ownSliceCap Loc lssl (DFrac.own 1) ∗
      "Hw2" ∷ slice.slice sl GoString k sl.len ↦*{dqs} ns ∗
      "Hp" ∷ osPathS R d dq j ∗ "Hperm" ∷ osCallPerm qc ∗ "Hn" ∷ osNames j N dqn h ∗
      "Hop" ∷ walOpenedRcs write d ns is (sint.nat jj) frs lfs rcs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.nat jj ≤ ns.length ∧ frs.length = sint.nat jj ∧
        lfs.length = sint.nat jj ∧ rcs.length = sint.nat jj⌝)
      $$ [i name rcs Hrc0 Hrcc0 rs Hrs0 Hrsc0 ls Hls0 Hlsc0 Hw2 Hp Hperm Hn]
  · iexists W64 0, _, rc0, rs0, ls0, [], [], []
    simp only [named, List.replicate_zero, List.map_nil]
    iframe
    isplitl []
    · unfold walOpenedRcs; simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    exact ⟨by decide, Nat.zero_le _, rfl, rfl, rfl⟩
  have hnsl : ns.length = sint.nat sl.len - sint.nat k := by
    rw [← hns, List.length_drop, Hsll.1]
  wp_for IH
  obtain ⟨Hj0, Hjl, Hfl, Hll, Hrl⟩ := Hj
  wp_if_destruct
  · have hjlt : sint.nat jj < ns.length := by
      have : sint.Z jj < sint.Z (sl.len - k) := by
        first | exact Hif | (revert Hif; simp)
      rw [hnsl]; word
    obtain ⟨b, hb⟩ := walOpen_getElem? ns (sint.nat jj) hjlt
    obtain ⟨i, hi⟩ := walOpen_getElem? is (sint.nat jj) (by omega)
    obtain ⟨hbN, hbok, hbl, hbi⟩ := hnames _ b i hb hi
    have hns62 : ns.length < 2 ^ 63 := by
      rw [hnsl]; have : sint.nat sl.len < 2 ^ 63 := by word
      omega
    have hjz : sint.Z jj < sint.Z (sl.len - k) :=
      walOpen_lt_sub jj k sl.len hk0 hkz Hj0 (hnsl ▸ hjlt)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, hjz⟩)]
    wp_apply wp_load_slice_index (slice.slice sl GoString k sl.len) (sint.Z jj) ns dqs b Hj0 $$ [Hw2] as Hw2
    · iframe; ipureintro; exact hb
    try wp_auto
    wp_apply wp_slice_literal (V := GoString) [d, b]
    isplitr
    · ipureintro; rfl
    iintro %jsl ⟨Hjsl, -⟩
    (try wp_auto)
    wp_apply wp_Join _ [d, b] _ (by simp; omega) $$ [$Hjsl] as %pth ⟨%hpth, -⟩
    rw [join_child hclean hbok] at hpth
    subst hpth
    (try wp_auto)
    ihave #Hfu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
    · iPkgInit
    cases write
    · sorry
    · (try wp_auto)
      wp_apply wp_TryLock (child d b) (W64 2) (W32 384) _ Unit _ _
          (walOpen_triple R d b dq j i N dqn h qc (W64 2)
            (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hbok hbN hbi)
        $$ [Hp Hn Hperm] as %lf %err ⟨Hpost, Herr⟩
      · isplitl []; · iexact Hinv
        isplitl []; · iexact Hfu
        isplitl []; · iexact Hinv
        isplitl []; · iexact Hsi
        iframe
      iunfold fileutil.lockPost at Hpost
      icases Hpost with ⟨%x, (⟨%he, ⟨Hp, Hn, Hperm⟩, %f, %fd, %i', %hc, #Hlf, Hf, Ho, Hfd⟩ | ⟨%he, %b', ⟨Hp, Hn, Hperm⟩⟩)⟩
      · subst he
        obtain ⟨hfd0, hii⟩ := hc
        rw [hii]
        (try wp_auto)
        wp_apply wp_slice_literal (V := Loc) [lf]
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        wp_apply wp_slice_append $$ [$Hls $Hlsc $Hl1] as %lssl' ⟨Hls, Hlsc, -⟩
        (try wp_auto)
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf]
        isplitr
        · ipureintro; rfl
        iintro %r1 ⟨Hr1, -⟩
        wp_apply wp_slice_append $$ [$Hrc $Hrcc $Hr1] as %rcsl' ⟨Hrc, Hrcc, -⟩
        (try wp_auto)
        ihave #Hlf2 := Hlf
        iunfold fileutil.lockedFile at Hlf2
        iStructNamed Hlf2
        (try wp_auto)
        wp_apply wp_NewFileReader f as %rl Hrl
        ihave Hrl2 := (dfractional_update_into_persistently
          (typedPointsto (GF := GF) rl
            (go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f) (DFrac.own 1))
          (fun dq => typedPointsto (GF := GF) rl
            (go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f) dq)
          (DFrac.own 1)).update_into_persistently $$ Hrl
        iapply wp_fupd
        imod Hrl2 with #Hrl
        (try wp_auto)
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl]
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨Hs1, -⟩
        wp_apply wp_slice_append $$ [$Hrs $Hrsc $Hs1] as %rssl' ⟨Hrs, Hrsc, -⟩
        (try wp_auto)
        imodintro
        wp_for_post
        iframe
        iexists jj + W64 1, b, rcsl', rssl', lssl',
          frs ++ [⟨go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty, #rl⟩],
          lfs ++ [lf],
          rcs ++ [interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf]
        simp only [named, List.map_append, List.map_cons, List.map_nil]
        iframe
        have hj1 : sint.nat (jj + W64 1) = sint.nat jj + 1 :=
          walOpen_succ jj ns.length Hj0 hns62 hjlt
        rw [hj1]
        isplitl [Hop Hf Ho Hfd]
        · iapply (walOpenedRcs_snoc true d ns is (sint.nat jj) i frs lfs rcs _ lf _ hi ⟨Hfl, Hll, Hrl⟩)
          iframe Hop
          rw [List.getD_eq_getElem?_getD, hb, Option.getD_some]
          iunfold walOpenedRc
          iexists f, fd, rl
          iframe
          simp only [↓reduceIte, walReadFlag]
          iframe
          isplitr
          · ipureintro; exact hfd0
          isplitr
          · ipureintro; trivial
          isplitr
          · iexact Hrl
          isplitr
          · iexact Hlf
          ipureintro; trivial
        ipureintro
        simp only [List.length_append, List.length_singleton]
        refine ⟨by word, by omega, by omega, by omega, by omega⟩
      · sorry
  · have hjn : sint.nat jj = ns.length := by
      have : ¬ sint.Z jj < sint.Z (sl.len - k) := by
        intro h; apply Hif; first | exact h | rw [decide_eq_true h]
      rw [hnsl]; exact walOpen_eq_sub jj k sl.len hk0 hkz Hj0 (hnsl ▸ Hjl) this
    iapply HΦ
    ihave Hsl := (ownSlice_slice k sl.len sl dqs names ⟨hk0, hkz, Int.le_refl _⟩).2 $$ [Hw1 Hw2 Hw3]
    · rw [hsub, hns]; iframe
    iframe
    ileft
    iexists frs, lfs
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, by omega, by omega⟩
    iunfold walOpenedRcs at Hop
    rw [hjn, hlen, List.take_length]
    iapply (BigSepL.bigSepL_mono (fun {m x} _ => walOpenedRc_file (GF := GF) write d _ x _ _ _))
    iexact Hop

end proof

end EtcdGrove
end Perennial
