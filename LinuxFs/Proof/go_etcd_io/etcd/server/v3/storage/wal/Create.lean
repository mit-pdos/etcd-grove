/-
`wal.Create` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`). The callees' specs not yet proved
over `fsExt` are hypotheses (`CreateCallees.lean`; the W4 log lists them). **Unfinished**: the body is
proved through the call of `renameWAL` and its committed-error arm; its other three arms are `sorry` (the W4 log, nineteenth session, says what is left). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Create
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.syncDir
public import LinuxFs.Spec.path.filepath.Clean
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.go_uber_org.zap.String
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Int64
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateTmp
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbsent
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbort
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenNames
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSeg
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLocked
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PreSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateHdr
public import LinuxFs.Proof.os.MkdirAllParts
public import Spec.fmt.SprintfWalName
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateRename
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCoh
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.AreaPath
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAreaBack
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLockedLeft

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
variable [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

set_option hygiene false in
/-- **An error exit after the segment's create** (the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the
segment's claim merged back, the abort), at the deferred calls; unhygienic: it names `Create`'s
hypotheses. -/
macro "create_seg_exit" : tactic => `(tactic| (
    wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd] as %cerr -
    · iframe; iframe #
    imod segClaim_back R J (walFileName 0 0) hJ (some (x0, s0, i)) hJs.2.2 CoPset.subseteq_top
      $$ Hsi HJr Ho with ⟨%hJ', %hJf, HJ⟩
    ihave Ht : tmpDirH jr (tmpName nm) hT3 $$ [HT HJ]
    · unfold tmpDirH; rw [hJs.1]; unfold tmpSub; iframe HT; iexists hJ'; iframe HJ
      ipureintro; exact hJf
    try wp_auto
    wp_apply +noauto wp_removeAllTmp wp_RmAbs wp_RmDir r (tmpName nm) R jr (e + a') hT3
      (tmpName_nameOk hnmO) $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
    · iframe; iframe #
    icases Ht with ⟨%hT4, Ht⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod create_abortTmp walCodec Mr R jr r N h cl nm hT4 Wn hok hnm hNnm hself
      $$ Hinv Hsi Hnc Hu HN Ht Hcl Hsf
      with ⟨Hnc, Hu, Hres⟩
    iframe Hnc
    imodintro
    try wp_auto
    iapply HΦ
    iframe
    iright; ileft
    iframe
    ipureintro; intro hc; cases hc))

-- (the proof term's instantiation at the end of the declaration exceeds the default budget)
set_option maxHeartbeats 1000000 in
theorem wal.Create.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Exist : wal.Exist.specCreate (GF := GF) walCodec Mr)
    (wp_FExist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_RmAbs : os.RemoveAll.specAbsentS (GF := GF) (hG := hG))
    (wp_RmDir : os.RemoveAll.specDirS (GF := GF) (hG := hG))
    (wp_CDA : fileutil.CreateDirAll.specTmp (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_SprintfWal : fmt.SprintfWalName.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_cNWF : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF) (hG := hG))
    (wp_OpenC : os.OpenFile.specCreateSnc (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_CloseC : os.File.Close.specClosed (GF := GF) (hG := hG))
    (wp_Prealloc : go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.spec (GF := GF) (hG := hG))
    (wp_newFileEncoder : go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder.spec (GF := GF)
      (hG := hG))
    (wp_saveCrc : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.spec (GF := GF) (hG := hG))
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG (GF := GF) (hG := hG))
    (wp_SaveSnapPre : go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.specPre (GF := GF)
      (hG := hG) Mr)
    (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (wp_Fdatasync : go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.spec (GF := GF) (hG := hG))
    (wp_syncDir : go_etcd_io.etcd.server.v3.storage.wal.syncDir.spec (GF := GF) (hG := hG))
    (_wp_renameWAL : go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.spec (W := W) P Mr) :
    wal.Create.spec (GF := GF) P Mr := by
  intro lg R jr r dir nm mp md qp Q hin hnmO hdl hr hmp hmd hMr
  wp_start as ⟨#Hzap, #Hmd, #Hok, #Hdd, Hp, Hres, Hperm, Hu, Hau⟩
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply wp_Exist R jr r dir nm qp hin hnmO $$ [Hp Hres Hperm Hu] as %bx ⟨Hp, Hres, Hperm, Hu⟩
  · iframe; iframe #
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨#Hbin, #Herrs, #Hfmt, -, -, #Hsync, #Hproto, #Hfu, -, -, -, -, #Hos, #Htime, -, #Hfp, #Hzp, -, -, -, -, -, -, -⟩
  cases bx
  rotate_left
  · -- `Exist(dir)`: `os.ErrExist`, nothing done
    ihave #Hosf : (iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
        (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
        (∃ e : GoInterface, typedPointsto (globalAddr os.ErrNotExist) e DFrac.discard) ∗
        ∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) :
        IProp GF) $$ []
    · iapply isPkgInit_access $$ Hos
    icases Hosf with ⟨-, ⟨%ee, %hee, #Hee⟩, -, -⟩
    try wp_auto
    iapply HΦ
    iframe
    iright; ileft
    iframe
    ipureintro; exact hee
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  ihave %hrc := osPathS_cleanAbs' R r _ jr $$ Hp
  have hdc := dir_child hin
  subst hdc
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  wp_apply wp_Clean (child r nm) as %cr %hcr
  rw [clean_child hrc hnmO] at hcr
  subst hcr
  try wp_auto
  rw [tmp_path]
  -- the claim on `nm.tmp`, off the area claim (`walInvBody_drop`), with what it holds
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb, -⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  have hnm := hin.1
  have hNt : N.Mem (tmpName nm) := areaOk_tmp hok hnm
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod osNames_self R jr N _ h CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself⟩
  imod walInv_absent walCodec Mr R jr r N _ h Wn (child r nm) nm md Q hin (hok.1 nm hnm)
    $$ Hinv Hsi Hnc Hau HN Hsf with ⟨Hnc, Hau, HN, Hsf, %hnmA⟩
  obtain ⟨hNnm, hnmA⟩ := hnmA
  imod walInv_drop walCodec Mr R jr r N h nm (tmpName nm) ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm hNt
    (tmpName_walNameP nm) (tmpName_not_walName nm) (tmpName_areaSlot hnm) $$ Hinv Hsi Hnc Hu HN
    with ⟨Hnc, Hu, HN, HT⟩
  iframe Hnc
  imodintro
  icases area_takeTmp N h cl nm Wn hok hnm $$ Hcl with ⟨Hts, Hcl⟩
  have hTt : (h.restrict jr (N.inter [tmpName nm])).cur !! tmpName nm = h.cur !! tmpName nm := by
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ ((NameSet.mem_inter _ _ _).2 ⟨hNt, List.mem_singleton_self _⟩)]
  ihave Ht : tmpDirH jr (tmpName nm) (h.restrict jr (N.inter [tmpName nm])) $$ [HT Hts]
  · unfold tmpDirH; rw [hTt]; iframe
  wp_apply wp_existTmp wp_FExist r (tmpName nm) R jr qp _ 1 (tmpName_nameOk hnmO) $$ [Hp Ht Hperm]
    as %bt ⟨Hp, Ht, Hperm⟩
  · iframe; iframe #
  -- a leftover `nm.tmp`: `RemoveAll`
  ihave Ht : (∃ hT', tmpDirH jr (tmpName nm) hT') $$ [Ht]
  · iexists _; iexact Ht
  cases bt
  rotate_left
  try wp_auto
  icases Ht with ⟨%hT0, Ht⟩
  wp_apply wp_removeAllTmp wp_RmAbs wp_RmDir r (tmpName nm) R jr qp hT0 (tmpName_nameOk hnmO)
    $$ [Hp Ht Hperm] as %err ⟨Hp, Hperm, Ht, -⟩
  · iframe; iframe #
  cases err
  case ok ei =>
    -- `RemoveAll` failed: nothing done, `nm.tmp` merged back
    icases Ht with ⟨%hT1, Ht⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod create_abortTmp walCodec Mr R jr r N h cl nm hT1 Wn hok hnm hNnm hself
      $$ Hinv Hsi Hnc Hu HN Ht Hcl Hsf
      with ⟨Hnc, Hu, Hres⟩
    iframe Hnc
    imodintro
    try wp_auto
    iapply HΦ
    iframe
    iright; ileft
    iframe
    ipureintro; intro hc; cases hc
  all_goals (
    try wp_auto
    icases Ht with ⟨%hT1, Ht⟩
    have htl : (child r (tmpName nm)).length < 2 ^ 60 := by
      simp [child, tmpName] at hdl ⊢; omega
    wp_apply wp_CDA lg R jr (child r (tmpName nm)) r (tmpName nm) qp hT1 rfl (tmpName_nameOk hnmO) htl
      $$ [Hp Hperm Ht] as %err ⟨Hp, Hperm, Hcda⟩
    · iframe; iframe #
    icases Hcda with (⟨%herr, %hT2, Ht⟩ | ⟨%herr, %hT2, %hJ, %J, %n0, %hJs, HT, HJ, #Hcm0⟩)
    · -- `CreateDirAll` failed: the deferred `RemoveAll(nm.tmp)`, then the abort
      cases err
      case nil => exact absurd rfl herr
      try wp_auto
      wp_apply wp_String as %f1 -
      wp_apply wp_String as %f2 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      wp_apply +noauto wp_removeAllTmp wp_RmAbs wp_RmDir r (tmpName nm) R jr qp hT2 (tmpName_nameOk hnmO)
        $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
      · iframe; iframe #
      icases Ht with ⟨%hT3, Ht⟩
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod create_abortTmp walCodec Mr R jr r N h cl nm hT3 Wn hok hnm hNnm hself
        $$ Hinv Hsi Hnc Hu HN Ht Hcl Hsf
        with ⟨Hnc, Hu, Hres⟩
      iframe Hnc
      imodintro
      try wp_auto
      iapply HΦ
      iframe
      iright; ileft
      iframe
      ipureintro; intro hc; cases hc
    subst herr
    obtain ⟨hJs1, hJs2, hJs3, hJfr⟩ := hJs
    replace hJs : hT2.cur !! tmpName nm = some (Node.dir J) ∧ hT2.next ≤ n0 ∧ hJ.cur = ∅ :=
      ⟨hJs1, hJs2, hJs3⟩
    try wp_auto
    -- `p := filepath.Join(tmpdirpath, walName(0, 0))`
    wp_func_call
    wp_call
    try wp_auto
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.uint64 #(W64 0), interface.mkOk go.uint64 #(W64 0)]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    try wp_auto
    wp_apply wp_SprintfWal _ _ _ _ $$ [$Hasl] as %bw ⟨-, %hbw⟩
    rw [show fmt.walNameStr (W64 0) (W64 0) = walFileName 0 0 from
      (walFileName_walNameStr 0 0).symm] at hbw
    subst hbw
    try wp_auto
    wp_apply wp_slice_literal (V := GoString) [child r (tmpName nm), walFileName 0 0]
    isplitr
    · ipureintro; rfl
    iintro %jsl ⟨Hjsl, -⟩
    try wp_auto
    have hjl : ([child r (tmpName nm), walFileName 0 0].map List.length).sum + 2 < 2 ^ 62 := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, walFileName_length]
      omega
    have htc : filepath.CleanAbs (child r (tmpName nm)) := by
      have := filepath.cleanAbs_append r (tmpName nm) hrc (cleanSeg_of_nameOk (tmpName_nameOk hnmO))
      simpa [child, slashB] using this
    wp_apply wp_Join _ _ _ hjl $$ [$Hjsl] as %fpath ⟨%hfpath, -⟩
    rw [join_child htc (walFileName_nameOk 0 0)] at hfpath
    subst hfpath
    try wp_auto
    -- `createNewWALFile(p, false)`: the segment's name split off `J`'s claim, the spine to `nm.tmp`
    have hb0 := walFileName_nameOk 0 0
    have hSame : ((NameSet.except []).inter [walFileName 0 0]).Same (.only [walFileName 0 0]) :=
      fun b' => by
        rw [NameSet.mem_inter]
        simp only [NameSet.Mem, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
          _root_.true_and]
    have hcur0 : (hJ.restrict J ((NameSet.except []).inter [walFileName 0 0])).cur !!
        walFileName 0 0 = none := by
      simp only [NamesH.restrict]
      rw [restrictN_lookup _ _ _ ((NameSet.mem_inter _ _ _).2 ⟨by simp [NameSet.Mem], by simp⟩),
        hJs.2.2]
      rfl
    imod osNames_split R J (.except []) [walFileName 0 0] hJ CoPset.subseteq_top $$ Hsi HJ
      with ⟨HJ0, HJr⟩
    imod osNames_rekey R J _ (.only [walFileName 0 0]) _ hSame CoPset.subseteq_top $$ Hsi HJ0
      with HJ0
    obtain ⟨e, a', b', hqd, hqq⟩ := os.qp_common qp 1
    subst hqd
    icases (osPathS_frac R r e a' jr).1 $$ Hp with ⟨Hpe, Hpa⟩
    icases (osNames_join jr (.only [tmpName nm]) e b' hT2 hqq).2 $$ HT with ⟨HTe, HTb⟩
    ihave Hpc := osPathS_child R r (tmpName nm) (DFrac.own e) jr J hT2 (tmpName_nameOk hnmO) hJs.1
      $$ Hpe HTe
    wp_apply wp_createSeg wp_cNWF wp_OpenC R (child r (tmpName nm)) (DFrac.own e) J (walFileName 0 0) _ 1
      hb0 hcur0 $$ [Hpc Hperm HJ0] as %lf %err ⟨Hpc, Hperm, %o, Ho, Hm, Hcs⟩
    · iframe; iframe #
    icases os.osPathS_unchild R r (tmpName nm) jr J e a' (tmpName_nameOk hnmO) $$ [Hpc Hpa]
      with ⟨%hT3, Hp, HTe, %-⟩
    · iframe
    icases osNames_agree jr (.only [tmpName nm]) _ _ hT3 hT2 $$ HTe HTb with %he
    subst he
    ihave HT := (osNames_join jr (.only [tmpName nm]) e b' hT3 hqq).1 $$ [HTe HTb]
    · iframe
    icases Hcs with (⟨%herr, %f, %fd, %i, %hfi, #Hlf, Hf, Hoff, Hfd⟩ | %herr)
    rotate_left
    · -- the create failed: the segment's claim back, the deferred `RemoveAll(nm.tmp)`, the abort
      cases err
      case nil => exact absurd rfl herr
      imod segClaim_back R J (walFileName 0 0) hJ o hJs.2.2 CoPset.subseteq_top $$ Hsi HJr Ho
        with ⟨%hJ', %hJf, HJ⟩
      ihave Ht : tmpDirH jr (tmpName nm) hT3 $$ [HT HJ]
      · unfold tmpDirH; rw [hJs.1]; unfold tmpSub; iframe HT; iexists hJ'; iframe HJ
        ipureintro; exact hJf
      try wp_auto
      wp_apply wp_String as %f1 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      wp_apply +noauto wp_removeAllTmp wp_RmAbs wp_RmDir r (tmpName nm) R jr (e + a') hT3
        (tmpName_nameOk hnmO) $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
      · iframe; iframe #
      icases Ht with ⟨%hT4, Ht⟩
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod create_abortTmp walCodec Mr R jr r N h cl nm hT4 Wn hok hnm hNnm hself
        $$ Hinv Hsi Hnc Hu HN Ht Hcl Hsf
        with ⟨Hnc, Hu, Hres⟩
      iframe Hnc
      imodintro
      try wp_auto
      iapply HΦ
      iframe
      iright; ileft
      iframe
      ipureintro; intro hc; cases hc
    subst herr
    rcases o with _ | ⟨x0, s0, i0⟩
    · exact absurd (hfi.2.symm.trans hcur0) (by simp)
    obtain rfl : i = i0 := hfi.2
    isimp only [crMeta] at Hm
    try wp_auto
    -- `f.Seek(0, io.SeekEnd)`: the embedded `*os.File`'s (size 0 after the create)
    ihave #Hlt0 := Hlf
    iunfold fileutil.lockedFile at Hlt0
    iStructNamed Hlt0
    rw [MethodUnfold.method_unfold
      (t := go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) (m := go!"Seek")]
    wp_call
    try wp_auto
    have hnsz : Fs.newMeta.size ≤ 0xffffffff000 := by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
    have hino : (openFd i (wal.walOpenFlag false ||| W64 524288)).ino = i := rfl
    ihave Hm : osMeta (openFd i (wal.walOpenFlag false ||| W64 524288)).ino (DFrac.own 1) Fs.newMeta $$ [Hm]
    · rw [hino]; iexact Hm
    wp_apply (os.File.Seek.wp_end f fd _ (DFrac.own 1) (W64 0) (DFrac.own 1) (DFrac.own 1)
      (openFd i (wal.walOpenFlag false ||| W64 524288)) Fs.newMeta hfi.1 hnsz) $$ [$Hf $Hoff $Hfd $Hm] as %n %err ⟨Hf, Hfd, Hm, Hsk⟩
    · iframe #
    icases Hsk with (⟨%hn, Hoff⟩ | ⟨%herr, Hoff⟩)
    rotate_left
    · -- the seek failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      cases err
      case nil => exact absurd rfl herr
      try wp_auto
      wp_apply wp_String as %f1 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      create_seg_exit
    obtain ⟨rfl, rfl⟩ := hn
    try wp_auto
    -- `fileutil.Preallocate(f.File, SegmentSizeBytes, true)`: the segment grown to 64 MB of zeros
    ihave #Hwi : (wal.walInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    iunfold wal.walInit at Hwi
    icases Hwi with ⟨#Hcrct, #Hmet, #Hseg, -⟩
    try wp_auto
    have hwr : (openFd i (wal.walOpenFlag false ||| W64 524288)).writable = true := by
      simp only [openFd]; unfold wal.walOpenFlag O_RDONLY; decide
    ihave Hm : osMeta (openFd i (wal.walOpenFlag false ||| W64 524288)).ino (DFrac.own 1) Fs.newMeta $$ [Hm]
    · rw [hino]; iexact Hm
    wp_apply wp_Prealloc f fd _ (DFrac.own 1) (DFrac.own 1) (openFd i (wal.walOpenFlag false ||| W64 524288))
      Fs.newMeta _ (W64 64000000) true hfi.1 hwr (by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes,
        OsFile.ofDisk]) (by simp)
      (by simp) (by decide) (by decide)
      (fun _ => by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk])
      $$ [$Hf $Hoff $Hfd $Hm] as %perr ⟨Hf, Hoff, Hfd, Hpa⟩
    · iframe #
    simp only [preallocPost, ite_true]
    icases Hpa with ⟨%wsz, %hwsz, Hpa⟩
    cases perr
    case ok pe =>
      -- the preallocation failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      try wp_auto
      wp_apply wp_String as %f1 -
      wp_apply wp_Int64 as %f2 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      create_seg_exit
    obtain rfl : wsz = 64000000 := hwsz.2.2 rfl
    try wp_auto
    -- `w := &WAL{lg, dir, metadata}` (allocated), `newFileEncoder(f.File, 0)`
    irename lg => Hlgp
    irename metadata => Hmdp
    irename «$r0» => Hwal
    generalize «$r0_ptr» = wl at *
    iStructNamed Hwal
    imod sync.init_Mutex (BI.pure True : IProp GF) ⊤
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" wl) $$ mu [] with #Hmu
    · inext; ipureintro; trivial
    ihave #Henv : (encEnv : IProp GF) $$ []
    · iunfold encEnv; iframe #
    ihave #Hioi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil $$ []
    · iPkgInit
    ihave Hoff : os.ownOff f (W64 0) $$ [Hoff]
    · iexact Hoff
    wp_apply (wp_newFileEncoder f fd _ _ (W64 0) (W32 0) hfi.1 (by decide) (by decide))
      $$ [Hf Hoff] as %enc ⟨Henc, Hf, Hoff, %he⟩
    · iframe; iframe #
    try wp_auto
    -- `w.locks = append(w.locks, f)`
    wp_apply wp_slice_literal (V := Loc) [lf]
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    ihave Hls0 := ownSlice_nil (GF := GF) (V := Loc) (DFrac.own 1)
    ihave Hcap0 := ownSliceCap_nil (GF := GF) (V := Loc)
    wp_apply (wp_slice_append (V := Loc) slice.nil [] _ [lf] (DFrac.own 1)) $$ [Hl1]
      as %locks' ⟨Hls, Hcap, -⟩
    · iframe; iframe #
    try wp_auto
    -- the headers' stream over the segment's zeros, from offset 0
    have hFr := createStream_frames Mr md hMr
    have hL := createStream_fit Mr md hMr hmd
    have hnm0 : Fs.newMeta.size = 0 := by
      simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
    iunfold preGrown at Hpa
    icases Hpa with ⟨%m2, ⟨%hm2s, %hm2maps, -, %hgrow⟩, Hm2, Hz2⟩
    icases (osZerosA_unfold i _ _ (DFrac.own 1)).1 $$ Hz2 with ⟨%zs2, %hzs2, Hz2⟩
    have hlo2 : m2.lo ≤ m2.size :=
      hgrow.2 (by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk])
    have hmaps2 : m2.maps = ∅ := by
      rw [hm2maps]; simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
    ihave Hm2 : osMeta (openFd i (wal.walOpenFlag false ||| W64 524288)).ino (DFrac.own 1) m2 $$ [Hm2]
    · rw [hino]; iexact Hm2
    ihave Hz2 : osBytes (openFd i (wal.walOpenFlag false ||| W64 524288)).ino 0 (DFrac.own 1)
        (zs2.map (fun c => ((0 : w8), c))) $$ [Hz2]
    · rw [hino, ← hnm0]; iexact Hz2
    ihave HW0 := os.fileW_start f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
      (openFd i (wal.walOpenFlag false ||| W64 524288)) m2 0 (zs2.map (fun c => ((0 : w8), c)))
      hlo2 (Nat.zero_le _) (by simp [hzs2, hm2s, hnm0]) $$ [Hf Hfd Hoff Hm2 Hz2]
    · iframe
    ihave #Hws := os.File.writerStreamI wp_WriteAt f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
      (openFd i (wal.walOpenFlag false ||| W64 524288)) m2 (zs2.map (fun c => ((0 : w8), c)))
      (createStream Mr md).length hfi.1 hwr hmaps2 (by omega) $$ Hosi
    ihave #HwsP := (io.writerStream_P _ _ _ _).1 $$ Hws
    ihave HW0' : os.fileWI f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
      (openFd i (wal.walOpenFlag false ||| W64 524288)) m2 (zs2.map (fun c => ((0 : w8), c))) [] $$ [HW0]
    · iunfold os.fileWI; iframe; iframe #
    -- `saveCrc(0)`
    rw [show (W32 0) = 0#32 from rfl] at *
    wp_apply (wp_saveCrc wl enc (wal.fileWi f) _ _ (fun ys => ys.length ≤ (createStream Mr md).length)
        [] [] 0#32 0#32 (fun xs ys hp hy => Nat.le_trans hp.length_le hy) (by rw [hFr]; simp))
      $$ [HwsP] [encoder Henc HW0'] as %serr1 ⟨%pend1, Hencf, Henc, Hr1⟩
    · iexact HwsP
    · iframe; iframe #
    icases Hr1 with (⟨%ys1, ⟨%he1, %hys1⟩, HW1⟩ | ⟨%a1, %b1, ⟨%he1, -, -⟩, HB1⟩)
    rotate_left
    · -- `saveCrc` failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      rcases serr1 with ei | _
      rotate_left
      · exact absurd rfl he1
      iunfold os.fileBI at HB1
      icases HB1 with ⟨HB1, -⟩
      iunfold os.fileB at HB1
      icases HB1 with ⟨%o', %mb, %ysb, -, Hf, Hfd, -⟩
      try wp_auto
      create_seg_exit
    subst he1
    try wp_auto
    -- `encode(&Record{Type: MetadataType, Data: metadata})`
    unfold go_etcd_io.etcd.server.v3.storage.wal.MetadataType
    try wp_auto
    imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ «$v0» with #Ht1
    have hmdr : recSize (recOf ⟨metadataType, hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md, md⟩)
        < 2 ^ 47 := recSize_hdr _ _ _ (by decide) (by omega)
    wp_apply (wp_encode enc (wal.fileWi f) _ _ (fun ys => ys.length ≤ (createStream Mr md).length)
        ([] ++ ys1) pend1 (hash.crc32.crc32c 0#32 []) «$a0_ptr» metadataType md hmdr
        (fun xs ys hp hy => Nat.le_trans hp.length_le hy) (by
          have h1 := congrArg List.length hys1
          rw [hFr]; unfold snapFrame
          simp only [List.length_append, List.length_nil] at h1 ⊢; omega))
      $$ [HwsP] [Henc HW1 «$a0»] as %serr2 ⟨%pend2, Henc, -, Hr2⟩
    · iexact HwsP
    · iframe Henv Henc HW1
      iunfold encRecIn
      iexists _
      iframe «$a0»
      have hd : (recOf ⟨metadataType, 0#32, md⟩).data = some md := by
        simp [recOf, metadataType, crcType]
      rw [hd]
      have hmt : metadataType = W64 1 := rfl
      rw [hmt]
      isplitl
      · iexact Ht1
      isplitr
      · simp only [recBytes, recOf, metadataType, crcType]
        isplitr
        · ipureintro; exact hmp
        iexact Hmd
      · ipureintro; trivial
    icases Hr2 with (⟨%ys2, ⟨%he2, %hys2⟩, HW2⟩ | ⟨%a2, %b2, ⟨%he2, -, -⟩, HB2⟩)
    rotate_left
    · -- `encode` failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      rcases serr2 with ei | _
      rotate_left
      · exact absurd rfl he2
      iunfold os.fileBI at HB2
      icases HB2 with ⟨HB2, -⟩
      iunfold os.fileB at HB2
      icases HB2 with ⟨%o', %mb, %ysb, -, Hf, Hfd, -⟩
      try wp_auto
      create_seg_exit
    subst he2
    try wp_auto
    -- `SaveSnapshot(&walpb.Snapshot{Index: new(0), Term: new(0)})`: its record, then `sync`
    imod walSnapAt_lit Mr hMr «$a0_ptr» «$v0_ptr» «$v1_ptr» _ _ $$ «$a0» «$v0» «$v1» with #Hsnap
    ihave Hpre : walPreIn wl lg (child r nm) mp md enc lf f (W64 0) (W64 0)
        $$ [lg dir metadata unsafeNoSync enti snapi Hencf locks Hls Hcap]
    · iunfold walPreIn
      iexists locks'
      iframe; iframe #
      ipureintro; exact he
    ihave #Hpbu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil $$ []
    · iPkgInit
    have hlen1 := congrArg List.length hys1
    have hlen2 := congrArg List.length hys2
    have hsyncOk := os.fileWI_preSyncOk wp_Fdatasync f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1) (openFd i (wal.walOpenFlag false ||| W64 524288)) m2
      (zs2.map (fun c => ((0 : w8), c)))
    wp_apply (wp_SaveSnapPre wl lg (child r nm) mp md enc lf f (W64 0) (W64 0) _ _ _
        (createStream Mr md).length ([] ++ ys1 ++ ys2) pend2
        (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) «$a0_ptr» snapC0.model false
        (Or.inl (by simp [snapC0, WalSnapC.model])) (by
          rw [hFr]
          simp only [List.length_append, List.length_nil] at hlen1 hlen2 ⊢; omega)
        (by omega) hsyncOk)
      $$ [Hws] [Hpre Henc HW2] as %serr3 ⟨%snapi', %enti', Hpre, Hr3⟩
    · iexact Hws
    · iframe; iframe #
    icases Hr3 with (⟨%he3, Henc, HS⟩ | ⟨%he3, %c3, %pend3, Henc, HBW⟩)
    rotate_left
    · -- `SaveSnapshot` failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      rcases serr3 with ei | _
      rotate_left
      · exact absurd rfl he3
      ihave Hff : (os.ownFile f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (openFd i (wal.walOpenFlag false ||| W64 524288))) $$ [HBW]
      · icases HBW with (⟨%a3, %b3, HB⟩ | ⟨%o3, HW⟩)
        · iunfold os.fileBI at HB
          icases HB with ⟨HB, -⟩
          iunfold os.fileB at HB
          icases HB with ⟨%o', %mb, %ysb, -, Hf, Hfd, -⟩
          iframe
        · iunfold os.fileWI at HW
          icases HW with ⟨HW, -⟩
          iunfold os.fileW at HW
          icases HW with ⟨%mb, %ysb, -, Hf, Hfd, -⟩
          iframe
      icases Hff with ⟨Hf, Hfd⟩
      try wp_auto
      create_seg_exit
    subst he3
    try wp_auto
    iunfold os.fileS at HS
    icases HS with ⟨%mS, %ysS, %hokS, Hf, Hfd, Hoff, HmS, HbS, -⟩
    -- `syncDir(tmpdirpath)` (F-N1): `nm.tmp` fsynced
    imod osNames_next R jr _ _ hT3 CoPset.subseteq_top $$ Hsi HT with ⟨HT, #HlbT⟩
    icases (osPathS_frac R r e a' jr).1 $$ Hp with ⟨Hpe, Hpa⟩
    icases (osNames_join jr (.only [tmpName nm]) e b' hT3 hqq).2 $$ HT with ⟨HTe, HTb⟩
    ihave Hpc := osPathS_child R r (tmpName nm) (DFrac.own e) jr J hT3 (tmpName_nameOk hnmO) hJs.1
      $$ Hpe HTe
    wp_apply wp_syncDir (child r (tmpName nm)) R J (DFrac.own e) 1 hT3.next $$ [Hpc Hperm]
      as %serr4 ⟨Hpc, Hperm, Hsd⟩
    · iframe; iframe #
    icases os.osPathS_unchild R r (tmpName nm) jr J e a' (tmpName_nameOk hnmO) $$ [Hpc Hpa]
      with ⟨%hT5, Hp, HTe, %-⟩
    · iframe
    icases osNames_agree jr (.only [tmpName nm]) _ _ hT3 hT5 $$ HTb HTe with %he5
    subst he5
    ihave HT := (osNames_join jr (.only [tmpName nm]) e b' hT3 hqq).1 $$ [HTe HTb]
    · iframe
    icases Hsd with (%hse | ⟨%hse, #Hcm1⟩)
    · -- `syncDir` failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      rcases serr4 with ei | _
      rotate_left
      · exact absurd rfl hse
      try wp_auto
      wp_apply wp_String as %f1 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      create_seg_exit
    subst hse
    try wp_auto
    -- `J`'s claims: merged after the segment's create, split off the pipeline's names
    imod createJ_claims R J (walFileName 0 0) hJ x0 s0 i hJs.2.2 hJfr (walNameP_walFileName 0 0)
      CoPset.subseteq_top $$ Hsi HJr Ho with ⟨%hJ', HJx, HTmps, %hJf⟩
    obtain ⟨hJval, hJcur⟩ := hJf
    imod osNames_coh R J _ _ _ CoPset.subseteq_top $$ Hsi HJx with ⟨HJx, %hJcoh⟩
    imod osNames_next R J _ _ _ CoPset.subseteq_top $$ Hsi HJx with ⟨HJx, #HlbJ⟩
    imod osNames_rekey R J ((NameSet.except []).diff walTmps) (.except walTmps) _ (fun _ => Iff.rfl)
      CoPset.subseteq_top $$ Hsi HJx
      with HJx
    -- the minting: the creating claim `.only [nm, nm.tmp]`, the token
    have hNnm' : (N.diff [tmpName nm]).Mem nm :=
      (NameSet.mem_diff _ _ _).2 ⟨hNnm, by simpa using (tmpName_ne nm).symm⟩
    have hNt' : ¬ (N.diff [tmpName nm]).Mem (tmpName nm) := fun hm =>
      ((NameSet.mem_diff _ _ _).1 hm).2 (List.mem_singleton_self _)
    have hDe : (N.diff [tmpName nm]).diff [nm] ≠ .only [] := by
      apply nameSet_ne_empty (b := nm ++ go!"." ++ go!"a")
      have hl : ∀ t : GoString, t.length ≠ (nm ++ go!"." ++ go!"a").length → nm ++ go!"." ++ go!"a" ≠ t :=
        fun t ht he => ht (by rw [he])
      refine (NameSet.mem_diff _ _ _).2 ⟨(NameSet.mem_diff _ _ _).2 ⟨hok.2.1 nm _ hnm, ?_⟩, ?_⟩
      · simp only [List.mem_singleton]
        exact hl _ (by simp [tmpName])
      · simp only [List.mem_singleton]
        exact hl _ (by simp)
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_mint walCodec Mr R jr r (child r nm) nm (tmpName nm) (N.diff [tmpName nm])
      (h.restrict jr (N.diff [tmpName nm])) hT3 J walTmps
      (hJ'.restrict J ((NameSet.except []).diff walTmps)) ⊤ CoPset.subseteq_top walN_osShN_top hnm
      hNnm' hNt' hDe (tmpName_not_walName nm) (tmpName_walNameP nm) (walNameOk_not_tmps hnm)
      walTmps_not_wal (fun _ h => h) $$ Hinv Hsi Hnc Hu HN HT HJx with ⟨Hnc, %hC, Hcr, HNr, HC, HJx, %hCf⟩
    iframe Hnc
    imodintro
    imod create_J_ne R jr J [nm, tmpName nm] nm _ _ hC _ (by simp) (walNameOk_not_tmps hnm)
      CoPset.subseteq_top $$ Hsi HC HJx with ⟨%hJjr, HC, HJx⟩
    imod osNames_next R jr _ _ _ CoPset.subseteq_top $$ Hsi HC with ⟨HC, #HlbC⟩
    ihave #Hlb : osLogLb (max hC.next (hJ'.restrict J ((NameSet.except []).diff walTmps)).next) $$ []
    · rcases Nat.le_total hC.next (hJ'.restrict J ((NameSet.except []).diff walTmps)).next with hle | hle
      · rw [Nat.max_eq_right hle]; iexact HlbJ
      · rw [Nat.max_eq_left hle]; iexact HlbC
    have hctmp : hC.cur !! tmpName nm = some (.dir J) := by
      have := congrArg (fun x : NamesH => x.cur !! tmpName nm) hCf.1
      simp only [NamesH.restrict] at this
      rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), restrictN_lookup _ _ _ (by simp [NameSet.Mem]),
        hJs.1] at this
      exact this
    have hcnm : hC.cur !! nm = none := by
      have := congrArg (fun x : NamesH => x.cur !! nm) hCf.2.1
      have hm : ((N.diff [tmpName nm]).inter [nm]).Mem nm := (NameSet.mem_inter _ _ _).2 ⟨hNnm', by simp⟩
      simp only [NamesH.restrict] at this
      rw [restrictN_lookup _ _ _ hm, restrictN_lookup _ _ _ hm, restrictN_lookup _ _ _ hNnm', hnmA] at this
      exact this
    have hm2c : m2.cut = none := by
      rw [hgrow.1]; simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
    have hout : [] ++ ys1 ++ ys2 ++ pend2 ++
        snapFrame Mr (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) snapC0.model = createStream Mr md := by
      rw [hFr]
      simp only [List.nil_append] at hys1 ⊢
      rw [show ys1 ++ ys2 ++ pend2 = ys1 ++ (ys2 ++ pend2) by simp, hys2, ← List.append_assoc, hys1]
    have hokS' : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS := by
      rw [← hout]; exact hokS
    -- `J`'s claim: half to the update, half kept (the handle's)
    icases (osNames_frac J (.except walTmps) (1 : Qp).half (1 : Qp).half _).1 $$ [HJx] with ⟨HJh, HJx⟩
    · rw [Qp.half_add_half]; iexact HJx
    -- the update (`createFresh_osAUnc`), its result with the invariant (`createU`)
    ihave HP : walCreateP (child r nm) (.only [nm, tmpName nm]) hC md Q J walTmps
        (hJ'.restrict J ((NameSet.except []).diff walTmps)) (createSeg i mS ysS) $$ [Hcr Hau HJh HmS HbS]
    · unfold walCreateP createSeg
      rw [show i = (openFd i (walOpenFlag false ||| W64 524288)).ino from rfl]
      iframe
    ihave HU : createU Mr R jr r nm hC md Q J (hJ'.restrict J ((NameSet.except []).diff walTmps))
        (createSeg i mS ysS) none $$ [HP]
    · unfold createU; simp only [walCreateQ]; iframe Hinv HP
    ihave Hau := createU_none Mr R jr r nm md Q hC J hJ' i m2 mS zs2 ysS
      (max hC.next (hJ'.restrict J ((NameSet.except []).diff walTmps)).next) hin hnm hMr hmd hctmp hJjr
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) hJcoh hJval hJcur hokS' hm2s hm2c $$ HU
    -- the spine law's fractions: `d` twice of the area's spine (the invariant's lend,
    -- `walInv_areaPath`: one spine stays with the pipeline) and of the new name's claim
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_areaPath walCodec Mr R jr r $$ Hinv Hnc with ⟨Hnc, %qa, Hq⟩
    iframe Hnc
    imodintro
    obtain ⟨d, a1, b1, hd1, hd2⟩ := os.qp_common qa.half (1 : Qp).half.half
    have hd : d + (d + (b1 + b1)) = (1 : Qp).half := by
      rw [Qp.ext_iff] at hd2 ⊢
      simp only [Qp.val_add, Qp.val_half] at hd2 ⊢
      grind
    icases (osPathS_frac R r qa.half qa.half jr).1 $$ [Hq] with ⟨Hq1, Hq2⟩
    · rw [Qp.half_add_half]; iexact Hq
    icases (osPathS_frac R r d a1 jr).1 $$ [Hq1] with ⟨Hd1, Ha1⟩
    · rw [hd1]; iexact Hq1
    icases (osPathS_frac R r d a1 jr).1 $$ [Hq2] with ⟨Hd2, Ha2⟩
    · rw [hd1]; iexact Hq2
    ihave HSp : createSp Mr R jr r d $$ [Hd1 Hd2]
    · unfold createSp; iframe; iframe #
    -- `logDirPath := w.dir`
    iunfold walPreIn at Hpre
    icases Hpre with ⟨%locks, Hlgf, #Hzap', Hdirf, Hmdf, #Hmds, Huns, #Hmu', Henti, Hsnapi, Hencf,
      %hen, Hlocks, Hls, Hcap, #Hlt⟩
    try wp_auto
    ihave Hpre : walPreIn wl lg (child r nm) mp md enc lf f snapi' enti'
        $$ [Hlgf Hdirf Hmdf Huns Henti Hsnapi Hencf Hlocks Hls Hcap]
    · iunfold walPreIn
      iexists locks
      iframe; iframe #
      ipureintro; exact hen
    -- `w.renameWAL(tmpdirpath)`: the commit
    have hOk : RenameWALOk R jr J r (child r nm) nm (tmpName nm) (.only [nm, tmpName nm]) hC
        (max hC.next (hJ'.restrict J ((NameSet.except []).diff walTmps)).next) (DFrac.own d)
        (createU Mr R jr r nm hC md Q J (hJ'.restrict J ((NameSet.except []).diff walTmps))
          (createSeg i mS ysS))
        (createSp Mr R jr r d) (createSpR jr J nm (b1 + b1)) :=
      ⟨hin, hdl, hnmO, tmpName_nameOk hnmO, tmpName_ne nm, by simp [NameSet.Mem],
        by simp [NameSet.Mem], hctmp, hcnm,
        create_spine Mr R jr J r nm hC md Q _ _ _ d (b1 + b1) hd hnm hnmO,
        createU_none Mr R jr r nm md Q hC J hJ' i m2 mS zs2 ysS _ hin hnm hMr hmd hctmp hJjr
          (Nat.le_max_left _ _) (Nat.le_max_right _ _) hJcoh hJval hJcur hokS' hm2s hm2c⟩
    wp_apply _wp_renameWAL R jr J r (child r nm) nm (tmpName nm) (.only [nm, tmpName nm]) hC _
      (e + a') (DFrac.own d) wl lg mp md enc lf f snapi' enti' fd _ _ _ _ _ _ _ hOk
      $$ [Hp Hperm HC Hau HSp HTmps Hpre fp dirFile Henc Hf Hfd Hoff] as %w' %err Hpost
    · iframe; iframe #
      iunfold walLockIn
      iframe
    unfold renameWALPost
    icases Hpost with ⟨Hp, Hpost⟩
    icases Hpost with (⟨%herr, %x, %fp, %γ, %sz, %df, %dfd, HU, HSpR, Hpre, Hlk, Hfpf, Hpipe, Hmain,
        Ht1, Hdff, Hdf, Hdfd, Hsd, Hperm⟩ | ⟨%herr, %x, HU, HSpR, Hw, Hnmd, Hpw⟩ |
      ⟨%herr, HU, HC, Hperm, HSp, HTmps, -, Hll⟩ | ⟨%herr, %x, HU, HSpR, Hperm, Hll⟩)
    · -- committed, `w` returned: the parent's fsync, the registration, the handle (not yet)
      sorry
    · -- committed, a reopened WAL returned: `renameWALPost`'s arm 2 is pending (ledger 2026-11-14)
      sorry
    · -- not committed: the unminting step (the creating token, the update and both claims back; not
      -- yet written), the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      sorry
    -- committed, an error: the deferred `f.Close()` and `RemoveAll(nm.tmp)` (absent now), the new
    -- name registered, the area back; the client's `Q` and half the permission
    rcases err with ei | _
    rotate_left
    · exact absurd rfl herr
    try wp_auto
    wp_apply wp_String as %f1 -
    wp_apply wp_String as %f2 -
    wp_apply wp_Error as %f3 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #
    try wp_auto
    wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f fd _ _ $$ [Hll] as %cerr -
    · iframe; iframe #
    iunfold createSpR at HSpR
    icases HSpR with ⟨%hn, %ht, Hnm, Htmp, %hnt⟩
    try wp_auto
    wp_apply +noauto wp_RmAbs r (tmpName nm) jr R (e + a') (DFrac.own 1) ht (1 : Qp).half
      (tmpName_nameOk hnmO) hnt.2 $$ [Hp Htmp Hperm] as %err' ⟨Hp, Htmp, Hperm, -⟩
    · iframe; iframe #
    unfold createU
    icases HU with ⟨-, HQ⟩
    unfold walCreateQ
    icases HQ with ⟨HQ, -, -, Hlt, -, -, Hnf, -, %s', Hpast, %hs'⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_register walCodec Mr R jr r s' (child r nm) nm Wn (b1 + b1) hn hin hnmO
      (by rw [hs']; simp) $$ Hinv Hsi Hnc Hpast Hnf Hsf Hnm with ⟨Hnc, -, Hsf⟩
    imod create_areaBack walCodec Mr R jr r N h cl nm ht Wn (walLockedTok (W := W))
      walLockedTok_unlocked_excl hok hnm hself hnt.2 $$ Hinv Hsi Hnc Hlt HNr Htmp Hcl Hsf
      with ⟨Hnc, -, Hres⟩
    iframe Hnc
    imodintro
    try wp_auto
    iapply HΦ
    iframe
    iright; iright
    iframe
    ipureintro; intro hc; cases hc)

end proof

end EtcdGrove
end Perennial
