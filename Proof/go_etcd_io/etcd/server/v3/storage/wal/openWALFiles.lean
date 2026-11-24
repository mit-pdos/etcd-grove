/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/openWALFiles.lean` (W5 of
`notes/wal-fsext-plan.md`), over the callees' specs (`fileutil.TryLockFile`, `fileutil.NewFileReader`,
`filepath.Join`, `closeAll`, `fmt.ErrorfErrs`: hypotheses).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.closeAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile
public import Spec.fmt.ErrorfErrsTerm
public import Spec.errors.IsPathErrnoTerm
public import Proof.errors.ErrTree
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader
public import Spec.path.filepath.Join
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openWALFilesLemmas

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

theorem go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.wp_proof
    [os.Assumptions] [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (wp_TryLock : go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile.spec (GF := GF) (hG := hG))
    (wp_NewFileReader : go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_closeAll : go_etcd_io.etcd.server.v3.storage.wal.closeAll.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (wp_ErrorfT : fmt.ErrorfErrsTerm.spec (GF := GF) (hG := hG))
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG)) :
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
      "Hp" ∷ osPathS R d dq j ∗ "Hperm" ∷ osCallPerm (callKey R d) qc ∗ "Hn" ∷ osNames j N dqn h ∗
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
  iapply wp_fupd
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
    wp_apply wp_Join _ [d, b] _ (by simp [_root_.Perennial.strings.joinMax]; omega) $$ [$Hjsl] as %pth ⟨%hpth, -⟩
    rw [join_child hclean hbok] at hpth
    subst hpth
    (try wp_auto)
    ihave #Hfu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
    · iPkgInit
    cases write
    · (try wp_auto)
      wp_apply os.OpenFile.wp_fileS d b (W64 0) (W32 384) R j i N dq dqn h qc
          (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hbok hbN hbi
        $$ [Hp Hn Hperm] as %f %err ⟨Hp, Hn, Hperm, Hr⟩
      · isplitl []; · iexact Hinv
        isplitl []; · iexact Hsi
        iframe
      icases Hr with (⟨%fd, %hh, Hf, Ho, Hfd⟩ | ⟨%hh, Herr, %ee, %hee, #Hep, -⟩)
      · obtain ⟨rfl, hfd0⟩ := hh
        (try wp_auto)
        wp_apply wp_slice_literal (V := Loc) [null]
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        wp_apply wp_slice_append $$ [$Hls $Hlsc $Hl1] as %lssl' ⟨Hls, Hlsc, -⟩
        (try wp_auto)
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk (go.GoType.PointerType os.File.ty) #f]
        isplitr
        · ipureintro; rfl
        iintro %r1 ⟨Hr1, -⟩
        wp_apply wp_slice_append $$ [$Hrc $Hrcc $Hr1] as %rcsl' ⟨Hrc, Hrcc, -⟩
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
          lfs ++ [null],
          rcs ++ [interface.mkOk (go.GoType.PointerType os.File.ty) #f]
        simp only [named, List.map_append, List.map_cons, List.map_nil]
        iframe
        have hj1 : sint.nat (jj + W64 1) = sint.nat jj + 1 :=
          walOpen_succ jj ns.length Hj0 hns62 hjlt
        rw [hj1]
        isplitl [Hop Hf Ho Hfd]
        · iapply (walOpenedRcs_snoc false d ns is (sint.nat jj) i frs lfs rcs _ null _ hi ⟨Hfl, Hll, Hrl⟩)
          iframe Hop
          rw [List.getD_eq_getElem?_getD, hb, Option.getD_some]
          iunfold walOpenedRc
          iexists f, fd, rl, none, none
          iframe
          simp only [Bool.false_eq_true, ↓reduceIte, walReadFlag]
          isplitr
          · iapply fdLocksW_ro _ _ rfl
            iapply fdLocks_unlocked <;> rfl
          isplitr
          · ipureintro; exact hfd0
          isplitr
          · ipureintro; trivial
          isplitr
          · iexact Hrl
          ipureintro; simp
        ipureintro
        simp only [List.length_append, List.length_singleton]
        refine ⟨by word, by omega, by omega, by omega, by omega⟩
      · obtain ⟨hne, rfl⟩ := hh
        cases err with
        | nil => exact (hne rfl).elim
        | ok e =>
        ihave #Hok := walOpen_errOk e $$ Herr
        ihave #Hosp : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
        · iPkgInit
        ihave #Hterm := wp_Term (GoInterface.ok e) ee hee $$ Hosp Hep
        (try wp_auto)
        wp_apply wp_closeAll lg rcsl rcs (DFrac.own 1) $$ [Hrc Hop] as %e2 ⟨Hrc, -⟩
        · iframe
          isplitl []; · iexact Hlg
          isplitl []; · iexact Hinv
          iapply (walOpenedRcs_close false d ns is (sint.nat jj) frs lfs rcs Hrl (by omega)) $$ Hop
        (try wp_auto)
        wp_apply wp_slice_literal (V := GoAny) [interface.mkOk go.string #(child d b), interface.ok e]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_apply wp_ErrorfT _ _ [interface.mkOk go.string #(child d b), interface.ok e] [e] ?wf ?ww $$ [Hasl] as %e1 ⟨#He1, #He1t⟩
        case wf => errargs_wf
        case ww => wraps_le1
        · iframe
          iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => iprop(errOk (GF := GF) e ∗
            errTreeTerm (GoInterface.ok e)))).2
          iframe Hok Hterm
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        imodintro
        iapply HΦ
        ihave Hsl := (ownSlice_slice k sl.len sl dqs names ⟨hk0, hkz, Int.le_refl _⟩).2 $$ [Hw1 Hw2 Hw3]
        · rw [hsub, hns]; iframe
        iframe
        iright
        iexists e1
        isplitr
        · ipureintro; rfl
        isplitl []
        · iexact He1
        iright
        ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
        · iPkgInit
        iapply (errIsTerm_of_tree (GoInterface.ok e1)) $$ Herrs He1t
    · (try wp_auto)
      wp_apply wp_TryLock (child d b) (W64 2) (W32 384) _ Unit _ _
          (walOpen_triple R d b dq j i N dqn h qc (W64 2)
            (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hbok hbN hbi)
          (by decide)
        $$ [Hp Hn Hperm] as %lf %err ⟨Hpost, Herr⟩
      · isplitl []; · iexact Hinv
        isplitl []; · iexact Hfu
        isplitl []; · iPkgInit
        isplitl []; · iexact Hinv
        isplitl []; · iexact Hsi
        iframe
      iunfold fileutil.lockPost at Hpost
      icases Hpost with ⟨%x, (⟨%he, ⟨Hp, Hn, Hperm⟩, %f, %fd, %i', %lk0, %hc, #Hlf, Hf, Ho, Hfd, Hlk0, #Hkind⟩ | ⟨%he, %b', ⟨Hp, Hn, Hperm⟩⟩)⟩
      · subst he
        obtain ⟨hfd0, hii⟩ := hc
        rw [hii]
        ihave Hfd := lkFd_openW lk0 i _ fd true true rfl rfl $$ [$Hfd $Hlk0 $Hkind]
        icases Hfd with ⟨%lo, %lk, Hfd, Hlks⟩
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
        isplitl [Hop Hf Ho Hfd Hlks]
        · iapply (walOpenedRcs_snoc true d ns is (sint.nat jj) i frs lfs rcs _ lf _ hi ⟨Hfl, Hll, Hrl⟩)
          iframe Hop
          rw [List.getD_eq_getElem?_getD, hb, Option.getD_some]
          iunfold walOpenedRc
          iexists f, fd, rl, lo, lk
          iframe
          simp only [↓reduceIte, walReadFlag]
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
      · obtain ⟨hne, rfl⟩ := he
        icases Herr with (%h0 | ⟨%e, %he, #Hok⟩)
        · exact (hne h0).elim
        subst he
        (try wp_auto)
        wp_apply wp_closeAll lg rcsl rcs (DFrac.own 1) $$ [Hrc Hop] as %e2 ⟨Hrc, -⟩
        · iframe
          isplitl []; · iexact Hlg
          isplitl []; · iexact Hinv
          iapply (walOpenedRcs_close true d ns is (sint.nat jj) frs lfs rcs Hrl (by omega)) $$ Hop
        (try wp_auto)
        wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_apply wp_Errorf _ _ [interface.ok e] [e] ?wf $$ [Hasl] as %e1 #He1
        case wf => errargs_wf
        · iframe
          iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
          iexact Hok
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        imodintro
        iapply HΦ
        ihave Hsl := (ownSlice_slice k sl.len sl dqs names ⟨hk0, hkz, Int.le_refl _⟩).2 $$ [Hw1 Hw2 Hw3]
        · rw [hsub, hns]; iframe
        iframe
        iright
        iexists e1
        isplitr
        · ipureintro; rfl
        isplitl []
        · iexact He1
        ileft; ipureintro; rfl
  · have hjn : sint.nat jj = ns.length := by
      have : ¬ sint.Z jj < sint.Z (sl.len - k) := by
        intro h; apply Hif; first | exact h | rw [decide_eq_true h]
      rw [hnsl]; exact walOpen_eq_sub jj k sl.len hk0 hkz Hj0 (hnsl ▸ Hjl) this
    ihave ⟨Hop, #Hlk⟩ := walOpenedRcs_split write d ns is (sint.nat jj) frs lfs rcs $$ Hop
    ipersist rcs
    ipersist lg
    imod ownSlice_persist $$ Hrc with #Hrc
    imodintro
    iapply HΦ
    ihave Hsl := (ownSlice_slice k sl.len sl dqs names ⟨hk0, hkz, Int.le_refl _⟩).2 $$ [Hw1 Hw2 Hw3]
    · rw [hsub, hns]; iframe
    iframe
    ileft
    iexists frs, lfs
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, by omega, by omega⟩
    isplitl [Hop]
    · rw [hjn, hlen, List.take_length] at *
      iexact Hop
    iunfold wal.walCloser
    isplitr
    · ipureintro; nofun
    iintro !> %Φ'
    iintro !> Hcl HΦ'
    rw [← recv_eq_func_mk]
    wp_auto
    wp_apply wp_closeAll lg rcsl rcs DFrac.discard $$ [Hcl] as %e2 -
    · iframe Hrc
      isplitl []; · iexact Hlg
      isplitl []; · iexact Hinv
      iapply (walClose_rcFiles write is (sint.nat jj) frs lfs rcs Hfl Hrl (by omega))
      iframe Hlk Hcl
    (try wp_auto)
    iapply HΦ'
    ipureintro; trivial

end proof

end EtcdGrove
end Perennial
