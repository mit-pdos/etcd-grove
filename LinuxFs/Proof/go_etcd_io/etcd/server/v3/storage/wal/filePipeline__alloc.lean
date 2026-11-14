/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/filePipeline__alloc.lean`:
`fmt.wp_SprintfTmp` (`pipeTmp_sprintf`), `filepath.Join` (`join_child`: the directory, a path in
the shared mode, is clean and absolute), `createNewWALFile` of the pipeline's name (`wp_createTmp`,
`PipeLemmas.lean`), the field load `lf.File`, `fileutil.Preallocate` from size 0 (`preGrown`: the
file's bytes a zero run); on its error the `zap` logging, the promoted `(*os.File).Close`, and the
claim back with the file (`tmpClaim`'s `trFile`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__alloc
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.os.File__Close
public import Proof.fmt.SprintfTmp
public import Spec.go_uber_org.zap.Logger__Error
public import LinuxFs.Spec.go_uber_org.zap.Int64
public import LinuxFs.Spec.go_uber_org.zap.Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [os_fa : os.file.FieldAssumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.wp_proof
    (wp_create : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF)
      (hG := hG))
    (wp_open : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Preallocate : go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_LError : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.spec (GF := GF) (hG := hG) := by
  intro fp γ R dir dq j sz n hn
  wp_start as ⟨#Hfp, Hcnt, Hc, Hres⟩
  iunfold isFilePipe at Hfp
  icases Hfp with ⟨%lg, #Hlg, #Hdir, #Hsz, #Hfc, #Hec, #Hdc, #Hhsn, #Hspsc, #Hbc, #Hlgok, #Hos,
    #Hsi, #Hpkg, %hsz⟩
  iunfold pipeRes at Hres
  icases Hres with ⟨Hperm, Hp⟩
  ihave %hclean := osPathS_cleanAbs R dir dq j $$ Hp
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.int #(BitVec.srem (W64 n) (W64 2))]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  (try wp_auto)
  wp_apply fmt.wp_SprintfTmp _ _ _ $$ [$Hasl] as %nm ⟨-, %hnm⟩
  rw [pipeTmp_sprintf n hn] at hnm
  subst hnm
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [dir, pipeTmp n]
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  (try wp_auto)
  wp_apply wp_Join _ [dir, pipeTmp n] _ (by
      have : (pipeTmp n).length = 5 := by unfold pipeTmp; split <;> rfl
      simp [this]; omega) $$ [$Hjsl] as %pth ⟨%hpth, -⟩
  rw [join_child hclean (pipeTmp_nameOk n)] at hpth
  subst hpth
  (try wp_auto)
  wp_apply wp_createTmp wp_create wp_open R dir dq j (pipeTmp n) (pipeTmp_nameOk n)
    $$ [$Hos $Hpkg $Hsi $Hp $Hperm $Hc] as %lf %e ⟨Hp, Hperm, Hr⟩
  icases Hr with (⟨%he, %f, %fd, %i, %h, #Hlf, Hf, Hoff, Hfd, Htr, Hn, %hfi⟩ | ⟨%he, Hc⟩)
  · subst he
    (try wp_auto)
    iunfold fileutil.lockedFile at Hlf
    iStructNamed Hlf
    wp_auto
    iunfold trFile at Htr
    icases Htr with ⟨%m, %xs, Hm, -, -, %hm⟩
    obtain ⟨-, hm0, hmaps, hcut0, hlo0, hzf0, hzp0⟩ := hm
    have hm0 := hm0 trivial
    obtain ⟨hfd, hcur⟩ := hfi
    wp_apply wp_Preallocate f fd (child dir (pipeTmp n)) (DFrac.own 1) (DFrac.own 1)
      (openFd i (wal.walOpenFlag true ||| W64 0x80000)) m (W64 0) sz true hfd (by unfold openFd; dsimp only; decide) hmaps
      (by decide) (by decide) hsz.1 hsz.2.1 (fun _ => by rw [hm0]; omega)
      $$ [$Hos $Hf $Hoff $Hfd Hm] as %e ⟨Hf, Hoff, Hfd, Hpost⟩
    · iapply (show osMeta (GF := GF) i (DFrac.own 1) m ⊢
        osMeta (openFd i (wal.walOpenFlag true ||| W64 0x80000)).ino (DFrac.own 1) m from .rfl) $$ Hm
    simp only [preallocPost, ite_true]
    icases Hpost with ⟨%w, %hw, Hg⟩
    iunfold preGrown at Hg
    icases Hg with ⟨%m', %hm', Hm', Hz⟩
    rw [hm0, Nat.sub_zero]
    cases e with
    | nil =>
      (try wp_auto)
      iapply HΦ
      iunfold pipeRes
      iframe Hperm Hp
      ileft
      isplitr
      · ipureintro; rfl
      rw [show W64 (n : Int) + W64 1 = W64 ((n : Int) + 1) by apply BitVec.eq_of_toNat_eq; simp [W64]; omega]
      iframe Hcnt
      iunfold pipeFile
      iexists f, fd, i, m', h
      iunfold fileutil.lockedFile
      iframe
      isplitl []
      · iexact Hlf
      isplitl [Hz]
      · rw [hm'.1]; iexact Hz
      ipureintro
      refine ⟨hfd, hm'.2.1.trans hmaps, hcur, hm'.2.2.2.1.1.trans hcut0, hm'.2.2.2.1.2.1 (by omega), ?_, ?_,
        hm'.2.2.2.2 ⟨rfl, hzp0 trivial⟩⟩
      · rw [hm'.1, hw.2.2 rfl]
        have := BitVec.toInt_eq_toNat_cond sz
        split at this <;> omega
      · rw [hm'.1, hw.2.2 rfl]
        have := BitVec.toInt_eq_toNat_cond sz
        split at this <;> omega
    | ok ei =>
      (try wp_auto)
      wp_apply wp_Int64 as %f1 -
      (try wp_auto)
      wp_apply wp_Error as %f2 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_LError lg _ _ $$ []
      · iexact Hlgok
      (try wp_auto)
      iStructNamed Hlf
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply wp_Close f fd _ _ $$ [$Hos $Hf $Hfd] as %ce -
      (try wp_auto)
      iapply HΦ
      iunfold pipeRes
      iframe Hperm Hp
      iright
      isplitr
      · ipureintro; exact fun h => by cases h
      iframe Hcnt
      iunfold tmpClaim
      iexists h
      iframe Hn
      rw [hcur]
      simp only [tmpEnt]
      icases (osZerosA_unfold i 0 w (DFrac.own 1)).1 $$ Hz with ⟨%zs, %hzs, Hz⟩
      iunfold trFile
      iexists m', zs.map (fun c => ((0 : w8), c))
      iframe Hm' Hz
      isplitl []
      · iapply mcellsAny_empty m'.maps (hm'.2.1.trans hmaps)
      ipureintro
      refine ⟨by simp [hzs, hm'.1], fun h => h.elim, hm'.2.1.trans hmaps, hm'.2.2.2.1.1.trans hcut0,
        hm'.2.2.2.1.2.1 (by omega), hm'.2.2.2.1.2.2 hzf0, fun h => h.elim⟩
  · cases e with
    | nil => exact absurd rfl he
    | ok ei =>
    (try wp_auto)
    iapply HΦ
    iunfold pipeRes
    iframe
    iright
    iframe
    ipureintro; exact he

end proof

end EtcdGrove
end Perennial
