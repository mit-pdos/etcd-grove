/-
`wal.Create` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`). The callees' specs not yet proved
over `fsExt` are hypotheses (`CreateCallees.lean`; the W4 log lists them). **Unfinished**: the body is
proved up to the frontier `sorry` (the W4 log, eleventh session, says where). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Create
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

theorem wal.Create.wp_proof (C : WalCodec) (Mr : WalMarshal)
    (wp_Exist : wal.Exist.specCreate (GF := GF) C Mr)
    (wp_FExist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_RmAbs : os.RemoveAll.specAbsentS (GF := GF) (hG := hG))
    (wp_RmDir : os.RemoveAll.specDirS (GF := GF) (hG := hG))
    (wp_CDA : fileutil.CreateDirAll.specTmp (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hErrExist : ⊢ isPkgInit (PROP := IProp GF) pkg_id.os -∗
      ∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) :
    wal.Create.spec (GF := GF) C Mr := by
  intro lg R jr r dir nm mp md qp Q hin hnmO hdl hr hmp
  wp_start as ⟨#Hzap, #Hmd, #Hok, #Hdd, Hp, Hres, Hperm, Hu, Hau⟩
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply wp_Exist R jr r dir nm qp hin $$ [Hp Hres Hperm Hu] as %bx ⟨Hp, Hres, Hperm, Hu⟩
  · iframe; iframe #
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, -, -, -, -, -, #Hfu, -, -, -, -, #Hos, -, -, #Hfp, #Hzp, -, -, -, -, -, -, -⟩
  cases bx
  rotate_left
  · -- `Exist(dir)`: `os.ErrExist`, nothing done
    ihave ⟨%ee, %hee, #Hee⟩ := hErrExist $$ Hos
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
  imod walInv_absent C Mr R jr r N _ h (child r nm) nm md Q hin hNnm $$ Hinv Hsi Hnc Hau HN
    with ⟨Hnc, Hau, HN, %hnmA⟩
  imod walInv_drop C Mr R jr r N h nm (tmpName nm) ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm hNt
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
    imod create_abortTmp C Mr R jr r N h cl nm hT1 hok hnm hself $$ Hinv Hsi Hnc Hu HN Ht Hcl
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
      imod create_abortTmp C Mr R jr r N h cl nm hT3 hok hnm hself $$ Hinv Hsi Hnc Hu HN Ht Hcl
        with ⟨Hnc, Hu, Hres⟩
      iframe Hnc
      imodintro
      try wp_auto
      iapply HΦ
      iframe
      iright; ileft
      iframe
      ipureintro; intro hc; cases hc
    sorry)

end proof

end EtcdGrove
end Perennial
