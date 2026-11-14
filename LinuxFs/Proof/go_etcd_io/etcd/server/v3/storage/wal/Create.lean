/-
`wal.Create` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`). The callees' specs not yet proved
over `fsExt` are hypotheses (`CreateCallees.lean`; the W4 log lists them). **Unfinished**: the body is
proved up to the frontier `sorry` (the W4 log, eleventh session, says where). Lean-first.
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
public import LinuxFs.Proof.os.MkdirAllParts
public import Spec.fmt.SprintfWalName

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

theorem wal.Create.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Exist : wal.Exist.specCreate (GF := GF) walCodec Mr)
    (wp_FExist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_RmAbs : os.RemoveAll.specAbsentS (GF := GF) (hG := hG))
    (wp_RmDir : os.RemoveAll.specDirS (GF := GF) (hG := hG))
    (wp_CDA : fileutil.CreateDirAll.specTmp (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_SprintfWal : fmt.SprintfWalName.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_cNWF : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF) (hG := hG))
    (wp_OpenC : os.OpenFile.specCreateSnc (GF := GF) (hG := hG))
    (_wp_renameWAL : go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.spec (W := W) P Mr) :
    wal.Create.spec (GF := GF) P Mr := by
  intro lg R jr r dir nm mp md qp Q hin hnmO hdl hr hmp _hmd
  wp_start as ⟨#Hzap, #Hmd, #Hok, #Hdd, Hp, Hres, Hperm, Hu, Hau⟩
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply wp_Exist R jr r dir nm qp hin $$ [Hp Hres Hperm Hu] as %bx ⟨Hp, Hres, Hperm, Hu⟩
  · iframe; iframe #
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, #Hfmt, -, -, -, -, #Hfu, -, -, -, -, #Hos, -, -, #Hfp, #Hzp, -, -, -, -, -, -, -⟩
  cases bx
  rotate_left
  · -- `Exist(dir)`: `os.ErrExist`, nothing done
    ihave #Hosf : (iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
        ∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) :
        IProp GF) $$ []
    · iapply isPkgInit_access $$ Hos
    icases Hosf with ⟨-, %ee, %hee, #Hee⟩
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
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, HN, %hok, Hcl⟩
  have hnm := hin.1
  have hNnm : N.Mem nm := hok.1 nm hnm
  have hNt : N.Mem (tmpName nm) := areaOk_tmp hok hnm
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod osNames_self R jr N _ h CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself⟩
  imod walInv_absent walCodec Mr R jr r N _ h (child r nm) nm md Q hin hNnm $$ Hinv Hsi Hnc Hau HN
    with ⟨Hnc, Hau, HN, %hnmA⟩
  imod walInv_drop walCodec Mr R jr r N h nm (tmpName nm) ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm hNt
    (tmpName_walNameP nm) (tmpName_not_walName nm) (tmpName_areaSlot hnm) $$ Hinv Hsi Hnc Hu HN
    with ⟨Hnc, Hu, HN, HT⟩
  iframe Hnc
  imodintro
  icases area_takeTmp N h cl nm hok hnm $$ Hcl with ⟨Hts, Hcl⟩
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
    imod create_abortTmp walCodec Mr R jr r N h cl nm hT1 hok hnm hself $$ Hinv Hsi Hnc Hu HN Ht Hcl
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
      imod create_abortTmp walCodec Mr R jr r N h cl nm hT3 hok hnm hself $$ Hinv Hsi Hnc Hu HN Ht Hcl
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
      imod create_abortTmp walCodec Mr R jr r N h cl nm hT4 hok hnm hself $$ Hinv Hsi Hnc Hu HN Ht Hcl
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
    try wp_auto
    sorry)

end proof

end EtcdGrove
end Perennial
