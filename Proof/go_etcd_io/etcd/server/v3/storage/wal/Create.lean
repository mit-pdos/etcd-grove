/-
`wal.Create` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`; spec
`Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`). The callees' specs not yet proved
over `fsExt` are hypotheses (`CreateCallees.lean`; the W4 log lists them). **Unfinished**: the body is
proved through the call of `renameWAL`, its committed-error arm and its not-committed arm (the
unminting, `CreateUnmint.lean`); arm 1 builds the handle before naming (`walOpenWFU`, `CreateHandle.lean`);
both success arms then run one continuation (`create_named_cont`: the parent's fsync and the naming), whose
error exits run the deferred `cleanupWAL` (`create_cleanup`, over `CreateCleanup.lean`: the rename's law
`create_cleanupLaw` and `create_cleanBack` are `sorry` there; `notes/wal-units/create.md`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Create
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.syncDir
public import Spec.path.filepath.Clean
public import Spec.path.filepath.Join
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateTmp
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbsent
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbort
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenNames
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSeg
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLocked
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PreSync
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateHdr
public import Proof.os.MkdirAllParts
public import Spec.fmt.SprintfWalName
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateRename
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCoh
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.AreaPath
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAreaBack
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLockedLeft
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateUnmint
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamedStep
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleUnnamed
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FsyncS
public import Spec.path.filepath.Dir
public import Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCleanup
public import Spec.fmt.ErrorfErrs

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
variable [os_sem : os.Assumptions]
variable [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The probe's name is not the first segment's. -/
theorem touch_ne_walFileName : go!".touch" ≠ walFileName 0 0 := fun h => by
  have := walNameP_walFileName 0 0
  rw [← h] at this
  revert this; decide

set_option hygiene false in
/-- **An error exit after the segment's create** (the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the
segment's claim merged back, the abort), at the deferred calls; unhygienic: it names `Create`'s
hypotheses. -/
macro "create_seg_exit" : tactic => `(tactic| (
    ihave Hlks := fdLocksW_locks _ _ $$ Hlks
    wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd Hlks] as %cerr -
    · iframe; iframe #
    imod segClaim_back R J (walFileName 0 0) hJ (some (x0, s0, i)) hJs.2 CoPset.subseteq_top
      $$ Hsi HJr Ho with ⟨%hJ', %hJf, HJ⟩
    ihave Ht : tmpDirH jr (tmpName nm) hT3 $$ [HT HJ]
    · unfold tmpDirH; rw [hJs.1]; unfold tmpSub; iframe HT; iexists hJ'; iframe HJ
      rw [hJf.2 _ touch_ne_walFileName]
      isplitr
      · ipureintro; exact hJf.1
      unfold tmpEnt; iempintro
    ihave Ht := tmpDirH_any jr (tmpName nm) hT3 $$ Ht
    try wp_auto
    wp_apply +noauto wp_removeAllTmp wp_RmSub r (tmpName nm) R jr (e + a') hT3
      (tmpName_nameOk hnmO) $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
    · iframe; iframe #
    icases Ht with ⟨%hT4, Ht, -⟩
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

set_option hygiene false in
/-- `fmt.ErrorfErrs.spec`'s error arguments `[cei, pei]` (the cleanup's error, `Hcef`, and the parent
directory's, `Hpe`): `errOk` each. Unhygienic. -/
macro "create_errs_pre" : tactic => `(tactic| (
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ e => errOk (GF := GF) e)).2
    isplitr
    · first | (iapply errOk_of_fmtErrorOkOrNil; iexact Hcef) | (iapply errOk_of_fmtErrorOk; iexact Hcef)
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ e => errOk (GF := GF) e)).2
    isplitr
    · first | (iapply errOk_of_fmtErrorOkOrNil; iexact Hpe) | (iapply errOk_of_fmtErrorOk; iexact Hpe)
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro))

set_option hygiene false in
/-- **The deferred calls after the commit, on an error exit of the parent's sync** (the parent's
`OpenDir`, `Fsync` or `Close` failed, `perr = ok pei`; at the deferred cleanup closure, the handle
before naming `walOpenWFU P Mr w (child r nm) R d f` whole): `cleanupWAL` (`WAL.cleanupWAL.spec`) over
`Create`'s area resources (`createFr`) and the rename's law (`create_cleanupLaw`); `fmt.Errorf` of
its error (if any); the deferred `f.Close()` (the tail lock's file: open after a failed sync, closed
after `Close`); the deferred `RemoveAll(nm.tmp)` of the absent name; the area back: the name
registered and `nm.tmp` merged back (`walInv_register`, `create_areaBack`) when no rename was called,
`create_cleanBack` after one. Unhygienic: it names `Create`'s hypotheses. -/
macro "create_cleanup" w:term:max tf:term:max "(" fA:tacticSeq ")" "(" fB:tacticSeq ")"
    "(" fC:tacticSeq ")" : tactic => `(tactic| (
    wp_apply wp_cleanupWAL R jr r nm $w lg R d $tf
      (createFr R jr r nm (DFrac.own (e + a')) N h c hn cl Wn)
      (createFin R jr r nm (e + a') $tf N h cl Wn) hnmO
      $$ [Hw Hpw Hcp Hp HNr Hnm Hcl Hsf'] as %cerr Hcr
    · iframe; iframe #
      isplitl [Hp HNr Hnm Hcl Hsf']
      · unfold createFr; iframe
      iapply create_cleanupLaw Mr R jr r nm _ N h cl Wn c d hn J $tf hok hin.1 hNnm hnmO _hcq hnm.1
        $$ Hok
    icases Hcr with (⟨%hce, #Hcef, Hlt, Hnf, Hcp, Hfr, %fd', %nmf, %d', Hf', Hfd', Hlks'⟩ |
      ⟨%hce, #Hcef, Hlt, Hnf, Hcp, Hfr, -, %nmf, Hf'⟩ | ⟨Hfin, #Hcef⟩)
    · -- `Close` failed in its sync: no rename
      rcases cerr with cei | _
      rotate_left
      · exact absurd rfl hce
      try wp_auto
      wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok cei, GoInterface.ok pei]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      try wp_auto
      wp_apply wp_ErrorfErrs _ _ [GoInterface.ok cei, GoInterface.ok pei] [cei, pei] ?wf $$ [Hasl]
        as %efi -
      case wf => errargs_wf
      · iframe Hasl
        create_errs_pre
      try wp_auto
      ($fA)
      try wp_auto
      unfold createFr
      icases Hfr with ⟨Hp, HNr, Hnm, Hcl, Hsf'⟩
      wp_apply +noauto wp_RmAbs r (tmpName nm) jr R (e + a') (DFrac.own 1) ht (1 : Qp).half
        (tmpName_nameOk hnmO) hht $$ [Hp Htmp Hcp] as %err' ⟨Hp, Htmp, Hcp, -⟩
      · iframe; iframe #
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_register walCodec Mr R jr r s' (child r nm) nm Wn c hn hin hnmO
        (by rw [hs']; simp) ⟨J, hnm.1⟩ $$ Hinv Hsi Hnc Hpast Hnf Hsf' Hnm with ⟨Hnc, -, Hsf'⟩
      imod create_areaBack walCodec Mr R jr r N h cl nm ht Wn (walLockedTok (W := W))
        walLockedTok_exclX hok hin.1 hself hht $$ Hinv Hsi Hnc Hlt HNr Htmp Hcl Hsf'
        with ⟨Hnc, -, Hres⟩
      iframe Hnc
      imodintro
      try wp_auto
      iapply HΦ
      iframe
      iright; iright
      iframe
      ipureintro; intro hc; cases hc
    · -- `Close` returned an error: no rename
      rcases cerr with cei | _
      rotate_left
      · exact absurd rfl hce
      try wp_auto
      wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok cei, GoInterface.ok pei]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      try wp_auto
      wp_apply wp_ErrorfErrs _ _ [GoInterface.ok cei, GoInterface.ok pei] [cei, pei] ?wf $$ [Hasl]
        as %efi -
      case wf => errargs_wf
      · iframe Hasl
        create_errs_pre
      try wp_auto
      ($fB)
      try wp_auto
      unfold createFr
      icases Hfr with ⟨Hp, HNr, Hnm, Hcl, Hsf'⟩
      wp_apply +noauto wp_RmAbs r (tmpName nm) jr R (e + a') (DFrac.own 1) ht (1 : Qp).half
        (tmpName_nameOk hnmO) hht $$ [Hp Htmp Hcp] as %err' ⟨Hp, Htmp, Hcp, -⟩
      · iframe; iframe #
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_register walCodec Mr R jr r s' (child r nm) nm Wn c hn hin hnmO
        (by rw [hs']; simp) ⟨J, hnm.1⟩ $$ Hinv Hsi Hnc Hpast Hnf Hsf' Hnm with ⟨Hnc, -, Hsf'⟩
      imod create_areaBack walCodec Mr R jr r N h cl nm ht Wn (walUnlockedTokX (W := W))
        walUnlockedTokX_exclX hok hin.1 hself hht $$ Hinv Hsi Hnc Hlt HNr Htmp Hcl Hsf'
        with ⟨Hnc, -, Hres⟩
      iframe Hnc
      imodintro
      try wp_auto
      iapply HΦ
      iframe
      iright; iright
      iframe
      ipureintro; intro hc; cases hc
    · -- the rename was called: `createFin`; `retErr` the cleanup's error wrapped, or `perr`
      unfold createFin
      icases Hfin with ⟨Hp, Hcp, ⟨%nmf, Hf'⟩, HaL⟩
      ihave Hcp := (osCallPerm_split (L := hG.goose_localGS) (callKey R r) (1 : Qp).half (1 : Qp).half).1 $$ [Hcp]
      · rw [Qp.half_add_half]; iexact Hcp
      icases Hcp with ⟨Hcp, -⟩
      rcases cerr with cei | _
      all_goals try wp_auto
      all_goals try (
        wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok cei, GoInterface.ok pei]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        try wp_auto
        wp_apply wp_ErrorfErrs _ _ [GoInterface.ok cei, GoInterface.ok pei] [cei, pei] ?wf $$ [Hasl]
          as %efi -
        case wf => errargs_wf
        · iframe Hasl
          create_errs_pre)
      all_goals (
        try wp_auto
        ($fC)
        try wp_auto
        wp_apply +noauto wp_RmAbs r (tmpName nm) jr R (e + a') (DFrac.own 1) ht (1 : Qp).half
          (tmpName_nameOk hnmO) hht $$ [Hp Htmp Hcp] as %err' ⟨Hp, Htmp, Hcp, -⟩
        · iframe; iframe #
        iapply wp_notCrashed_acc _ _ rfl
        iintro Hnc
        imod create_cleanBack walCodec Mr R jr r nm N h cl Wn ht hok hin.1 hself hht $$ Hinv Hsi Hnc HaL Htmp
          with ⟨Hnc, Hres⟩
        iframe Hnc
        imodintro
        try wp_auto
        iapply HΦ
        iframe
        iright; iright
        iframe
        ipureintro; intro hc; cases hc)))

set_option hygiene false in
/-- **The continuation after a committed `renameWAL` that returned a WAL** (arms 1 and 2, at the
handle before naming `walOpenWFU P Mr w dir`, `walPurgeW w dir` and `createUH x`), in Go's order:
`w.dir` (`walOpenWFU_dirAcc`), `filepath.Dir` (`dir_child_model`), `OpenDir(r)` with the handle's
call-permission quarter lent (`walOpenWFU_permAcc`), `time.Now`, `Fsync` with `osLogLb (x.1 + 1)`, the
naming at its success (`walInv_named`), `walFsyncSec.Observe`, `dirCloser()`, then the deferred calls
in LIFO order (the cleanup closure and `f.Close` skipped, `RemoveAll(nm.tmp)` of the absent name),
`walOpenWFU_named`, `create_areaBack` (`T := walOpenWF`), `walPurgeW_fresh_lbs`. Unhygienic: it
names `Create`'s hypotheses. The error exits (`OpenDir`, `Fsync`, the close) log and run the
deferred cleanup (`create_cleanup`); `w`, `tf` are the handle and its pinned tail file, `fA`-`fC` the
deferred `f.Close()` after each of the cleanup's outcomes. -/
macro "create_named_cont" w:term:max tf:term:max "(" fA:tacticSeq ")" "(" fB:tacticSeq ")"
    "(" fC:tacticSeq ")" : tactic => `(tactic| (
    iunfold createUH at HUH
    icases HUH with ⟨HQ, ⟨%s', #Hpast, %hs'⟩, ⟨%c, %hn, Hnm, %hnm⟩, #HlbX, ⟨%ht, Htmp, %hht⟩, Hsf'⟩
    obtain ⟨_hcq, hnm⟩ := hnm
    icases walInv_roots _ _ _ _ _ $$ Hinv with %hWRc
    icases osPathS_callKey R r _ jr $$ Hp with ⟨Hp, %hkcR⟩
    try wp_auto
    -- `pdir, perr := fileutil.OpenDir(filepath.Dir(w.dir))`
    icases walOpenWFU_dirAcc P Mr $w (child r nm) _ _ _ $$ Hw with ⟨Hdir, Hw⟩
    try wp_auto
    wp_apply wp_Dir (child r nm) as %pd %hpd
    rw [dir_child_model hrc hnmO] at hpd
    subst pd
    ihave Hw := Hw $$ Hdir
    icases walOpenWFU_permAcc P Mr $w (child r nm) _ _ _ $$ Hw with ⟨Hperm, Hw⟩
    ihave Hperm := walPerm_ofW hWRc (child r nm) _ $$ Hperm
    ihave Hperm := osCallPerm_congr _ (hkcR nm) $$ Hperm
    wp_apply wp_OpenDir r R jr (DFrac.own (e + a')) (1 : Qp).half.half $$ [Hp Hperm]
      as %pf %perr ⟨Hp, Hperm, Hod⟩
    · iframe; iframe #
    icases Hod with (⟨%pfd, %hperr, Hpf, Hpfd⟩ | ⟨%hperr, #Hpe⟩)
    rotate_left
    · -- `OpenDir` failed: logged, then the deferred `cleanupWAL`
      ihave Hperm := osCallPerm_congr _ (hkcR nm).symm $$ Hperm
      ihave Hperm := walPerm_toW hWRc (child r nm) _ $$ Hperm
      ihave Hw := Hw $$ Hperm
      try wp_auto
      icases walOpenWFU_dirAcc P Mr $w (child r nm) _ _ _ $$ Hw with ⟨Hdir, Hw⟩
      rcases perr with pei | _
      rotate_left
      · exact absurd rfl hperr.1
      try wp_auto
      wp_apply wp_Dir (child r nm) as %pd -
      wp_apply wp_String as %f1 -
      try wp_auto
      wp_apply wp_String as %f2 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      ihave Hw := Hw $$ Hdir
      try wp_auto
      create_cleanup $w $tf ($fA) ($fB) ($fC)
    subst hperr
    try wp_auto
    wp_apply wp_Now as %t0 -
    try wp_auto
    wp_apply wp_FsyncDir pf pfd r (DFrac.own 1) R jr .idle (x.1 + 1) $$ [Hpf Hpfd] as %ferr
      ⟨Hpf, Hpfd, Hfr⟩
    · iframe; iframe #
    icases Hfr with (⟨%hfe, #Hpe⟩ | ⟨%hfe, #Hcm⟩)
    · -- `Fsync` failed: the parent closed (not by `dirCloser`, which would overwrite `perr`: the fork's
      -- fix, `nonissues/etcd-wal-create-parent-fsync-nil-nil.md`), logged, the deferred `cleanupWAL`
      replace hfe := hfe.1
      rcases ferr with pei | _
      rotate_left
      · exact absurd rfl hfe
      try wp_auto
      wp_apply os.File.Close.wp_dirS pf pfd r jr .idle $$ [Hpf Hpfd] as %cerr0 -
      · iframe; iframe #
      ihave Hperm := osCallPerm_congr _ (hkcR nm).symm $$ Hperm
      ihave Hperm := walPerm_toW hWRc (child r nm) _ $$ Hperm
      ihave Hw := Hw $$ Hperm
      icases walOpenWFU_dirAcc P Mr $w (child r nm) _ _ _ $$ Hw with ⟨Hdir, Hw⟩
      try wp_auto
      wp_apply wp_Dir (child r nm) as %pd -
      wp_apply wp_String as %f1 -
      try wp_auto
      wp_apply wp_String as %f2 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      ihave Hw := Hw $$ Hdir
      try wp_auto
      create_cleanup $w $tf ($fA) ($fB) ($fC)
    subst hfe
    try wp_auto
    -- `walFsyncSec.Observe(time.Since(start).Seconds())`
    ihave #Henv0 := Henv
    iunfold encEnv at Henv0
    icases Henv0 with ⟨-, -, -, #Htm, #Hmet0⟩
    iunfold wal.metricsInit at Hmet0
    icases Hmet0 with ⟨⟨%hfs, #Hhs, #Hhspec⟩, -, -⟩
    iunfold wal.histSpec at Hhspec
    wp_apply wp_Since as %dur -
    try wp_auto
    haveI _hni : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
    wp_pures
    wp_apply (wp_Seconds dur) as %fl -
    try wp_auto
    wp_apply Hhspec
    iclear Hhspec Hhs
    try wp_auto
    -- `dirCloser()`
    wp_apply os.File.Close.wp_dirS pf pfd r jr .idle $$ [Hpf Hpfd] as %cerr #Hpe
    · iframe; iframe #
    by_cases hce : cerr = interface.nil
    rotate_left
    · -- the close failed (`dirCloser` logged it): the deferred `cleanupWAL`
      rcases cerr with pei | _
      rotate_left
      · exact absurd rfl hce
      ihave Hperm := osCallPerm_congr _ (hkcR nm).symm $$ Hperm
      ihave Hperm := walPerm_toW hWRc (child r nm) _ $$ Hperm
      ihave Hw := Hw $$ Hperm
      icases walOpenWFU_dirAcc P Mr $w (child r nm) _ _ _ $$ Hw with ⟨Hdir, Hw⟩
      try wp_auto
      wp_apply wp_Dir (child r nm) as %pd -
      wp_apply wp_String as %f1 -
      try wp_auto
      wp_apply wp_String as %f2 -
      wp_apply wp_Error as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      ihave Hw := Hw $$ Hdir
      try wp_auto
      create_cleanup $w $tf ($fA) ($fB) ($fC)
    subst hce
    try wp_auto
    -- the deferred `RemoveAll(nm.tmp)` (absent)
    wp_apply +noauto wp_RmAbs r (tmpName nm) jr R (e + a') (DFrac.own 1) ht (1 : Qp).half.half
      (tmpName_nameOk hnmO) hht $$ [Hp Htmp Hperm] as %err' ⟨Hp, Htmp, Hperm, -⟩
    · iframe; iframe #
    ihave Hperm := osCallPerm_congr _ (hkcR nm).symm $$ Hperm
    ihave Hperm := walPerm_toW hWRc (child r nm) _ $$ Hperm
    ihave Hw := Hw $$ Hperm
    -- the success exit (after the parent's close: the twenty-seventh session): the parent's fsync names
    -- the WAL (`walInv_named`), and the name is registered now (`walInv_register`; design P,
    -- `notes/wal-units/create.md`), the handle sealed (`walOpenWFU_seal`)
    obtain ⟨hnc, ex, Ex, hlw, hEx⟩ := hnm
    icases walOpenWFU_seal P Mr $w (child r nm) _ _ _ $$ Hw with ⟨Hnf, Hw⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    icases (osNames_frac (L := hG.goose_localGS) jr (.only [nm]) c.half c.half hn).1 $$ [Hnm]
      with ⟨Hnm, Hnm2⟩
    · rw [Qp.half_add_half]; iexact Hnm
    imod walInv_register walCodec Mr R jr r s' (child r nm) nm Wn c.half hn hin hnmO
      (by rw [hs']; simp) ⟨J, hnc⟩ $$ Hinv Hsi Hnc Hpast Hnf Hsf' Hnm with ⟨Hnc, Hnf, Hsf'⟩
    imod walInv_named walCodec Mr R jr r (child r nm) nm s' (walDurFresh md) (.only [nm])
      (DFrac.own c.half) hn x.1 ex Ex J (x.1 + 1) hs' hin (by simp [NameSet.Mem]) hlw (by omega) hEx
      $$ Hinv Hsi Hnc Hpast Hnm2 Hcm Hnf with ⟨Hnc, -, #Hnamed, Hnf⟩
    iframe Hnc
    imodintro
    ihave Hw := Hw $$ Hnf Hnamed
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod create_areaBack walCodec Mr R jr r N h cl nm ht Wn (walOpenWF P Mr $w (child r nm))
      (walOpenWF_unlocked_exclX P Mr $w (child r nm)) hok hnm hself hht
      $$ Hinv Hsi Hnc Hw HNr Htmp Hcl Hsf' with ⟨Hnc, Hw, Hres⟩
    iframe Hnc
    imodintro
    ihave ⟨Hpw, Hlen, Hsyn⟩ := walPurgeW_fresh_lbs $w (child r nm) s' (walDurFresh md) hs' $$ Hpw Hpast
    try wp_auto
    iapply HΦ
    iframe
    ileft
    iframe
    iframe Hnamed
    ipureintro; rfl))

/-- The spine law's fractions (top-level: `grind` inside `wal.Create.wp_proof` produced a proof term the
kernel rejects). -/
theorem create_qp_twice {d b1 : Qp} (hd2 : d + b1 = (1 : Qp).half.half) :
    d + (d + (b1 + b1)) = (1 : Qp).half := by
  rw [Qp.ext_iff] at hd2 ⊢
  simp only [Qp.val_add, Qp.val_half] at hd2 ⊢
  grind

-- (the proof term's instantiation at the end of the declaration exceeds the default budget)
set_option maxHeartbeats 1000000 in
theorem wal.Create.wp_proof (P : WalPbIn GF) (Mr : WalMarshal) (hnil : WalPbIn.NilLaw P)
    (wp_Exist : wal.Exist.specCreate (GF := GF) walCodec Mr)
    (wp_FExist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_RmAbs : os.RemoveAll.specAbsentS (GF := GF) (hG := hG))
    (wp_RmSub : os.RemoveAll.specSubS (GF := GF) (hG := hG))
    (wp_CDA : fileutil.CreateDirAll.spec (GF := GF) (hG := hG))
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
    (wp_SaveSnap : go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (W := W) (Sio := WalFs.ioNone)
      P Mr)
    (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (wp_Fdatasync : go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.spec (GF := GF) (hG := hG))
    (wp_syncDir : go_etcd_io.etcd.server.v3.storage.wal.syncDir.spec (GF := GF) (hG := hG))
    (_wp_renameWAL : go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.spec (W := W) P Mr)
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_OpenDir : go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_FsyncDir : go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_cleanupWAL : go_etcd_io.etcd.server.v3.storage.wal.WAL.cleanupWAL.spec (W := W) P Mr)
    (wp_ErrorfErrs : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    wal.Create.spec (GF := GF) P Mr := by
  intro lg R jr r dir nm mp md qp Q Pv hin hnmO hdl hr hmp hmd hmdne hMr hnoerr
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
    icases Hres with (⟨-, Hres⟩ | ⟨%hb, -⟩)
    rotate_left
    · cases hb
    ihave ⟨%ee, %hee, #Hee⟩ := os.errExist_of_pkgInit $$ Hos
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
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb, -, #Hab⟩
  -- `Exist`'s `false`: `nm` free in the area (in the claim, absent, not registered)
  icases Hres with (⟨%hb, -⟩ | ⟨-, Hres⟩)
  · cases hb
  iunfold WalFs.walAreaResFree at Hres
  icases Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %a1, %a2, Hcl, %a3, %a4, %hfree⟩
  have hok : AreaOk N h cl Wn := ⟨a1, a2, a3, a4⟩
  obtain ⟨hNnm, hnmA, hnW⟩ := hfree
  have hnm := hin.1
  have hNt : N.Mem (tmpName nm) := areaOk_tmp hok hnm
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod osNames_self R jr N _ h CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself⟩
  imod walInv_drop walCodec Mr R jr r N h nm (tmpName nm) ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm hNt
    (tmpName_walNameP nm) (tmpName_not_walName nm) (tmpName_areaSlot hnm) $$ Hinv Hsi Hnc Hu HN
    with ⟨Hnc, Hu, HN, HT⟩
  iframe Hnc
  imodintro
  icases area_takeTmp N h cl nm Wn hok hnm $$ Hcl with ⟨Hts, Hcl⟩
  have hTt : (h.restrict jr (N.inter [tmpName nm])).cur !! tmpName nm = h.cur !! tmpName nm := by
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ ((NameSet.mem_inter _ _ _).2 ⟨hNt, List.mem_singleton_self _⟩)]
  -- the file system does not fail on `nm.tmp` and the area: `Exist`/`RemoveAll` of `nm.tmp` exact
  have hFt : FsNoErrAt (child r (tmpName nm)) :=
    ⟨hnoerr.1.mono (fun p hp => .inr (.inl (by rw [hp, tmp_path]))), by rw [← tmp_path]; exact hnoerr.2.1⟩
  have hFr : FsNoErrAt r :=
    ⟨hnoerr.1.mono (fun p hp => .inr (.inr hp)), pathFits_area hnoerr.2.2⟩
  ihave Ht : tmpAny jr (tmpName nm) (h.restrict jr (N.inter [tmpName nm])) $$ [HT Hts]
  · unfold tmpAny; rw [hTt]; iframe
  wp_apply wp_existTmpNE wp_FExist r (tmpName nm) R jr qp _ 1 (tmpName_nameOk hnmO) $$ [Hp Ht Hperm]
    as %bt ⟨Hp, Ht, Hperm, %hbt⟩
  · iframe; iframe #
  -- a leftover `nm.tmp`: `RemoveAll`
  ihave Ht : (∃ hT', tmpAny jr (tmpName nm) hT' ∗
      ⌜bt = false → FsNoErrAt (child r (tmpName nm)) → hT'.cur !! tmpName nm = none⌝) $$ [Ht]
  · iexists _; iframe Ht; ipureintro; exact hbt
  cases bt
  rotate_left
  try wp_auto
  icases Ht with ⟨%hT0, Ht, -⟩
  wp_apply wp_removeAllTmp wp_RmSub r (tmpName nm) R jr qp hT0 (tmpName_nameOk hnmO)
    $$ [Hp Ht Hperm] as %err ⟨Hp, Hperm, Ht, -⟩
  · iframe; iframe #
  cases err
  case ok ei =>
    -- `RemoveAll` failed: nothing done, `nm.tmp` merged back
    icases Ht with ⟨%hT1, Ht, -⟩
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
    icases Ht with ⟨%hT1, Ht, %hT1n⟩
    have hT1a : hT1.cur !! tmpName nm = none := by
      first | exact hT1n rfl hFt | exact hT1n rfl hFt hFr
    iunfold tmpAny at Ht
    icases Ht with ⟨Ht, -⟩
    have htl : (child r (tmpName nm)).length < 2 ^ 60 := by
      simp [child, tmpName] at hdl ⊢; omega
    wp_apply wp_CDA lg R jr (child r (tmpName nm)) r (tmpName nm) qp hT1 rfl (tmpName_nameOk hnmO) htl
      hT1a $$ [Hp Hperm Ht] as %err ⟨Hp, Hperm, Hcda⟩
    · iframe; iframe #
    icases Hcda with (⟨%herr, %hT2, Ht⟩ | ⟨%herr, %hT2, %hJ, %J, %nC, %hJs0, HT, HJ, -⟩)
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
      ihave Ht := tmpDirH_any jr (tmpName nm) hT2 $$ Ht
      wp_apply +noauto wp_removeAllTmp wp_RmSub r (tmpName nm) R jr qp hT2 (tmpName_nameOk hnmO)
        $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
      · iframe; iframe #
      icases Ht with ⟨%hT3, Ht, -⟩
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
    have hJs : hT2.cur !! tmpName nm = some (.dir J) ∧ hJ.cur = ∅ := ⟨hJs0.1, hJs0.2.2⟩
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
        hJs.2]
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
    icases osCallPerm_child R r (tmpName nm) _ jr 1 $$ Hpa Hperm with ⟨Hpa, Hperm⟩
    wp_apply wp_createSeg wp_cNWF wp_OpenC R (child r (tmpName nm)) (DFrac.own e) J (walFileName 0 0) _ 1
      hb0 hcur0 $$ [Hpc Hperm HJ0] as %lf %err ⟨Hpc, Hperm, %o, Ho, Hm, Hcs⟩
    · iframe; iframe #
    icases os.osPathS_unchild R r (tmpName nm) jr J e a' (tmpName_nameOk hnmO) $$ [Hpc Hpa]
      with ⟨%hT3, Hp, HTe, %-⟩
    · iframe
    icases osCallPerm_unchild R r (tmpName nm) _ jr 1 $$ Hp Hperm with ⟨Hp, Hperm⟩
    icases osNames_agree jr (.only [tmpName nm]) _ _ hT3 hT2 $$ HTe HTb with %he
    subst he
    ihave HT := (osNames_join jr (.only [tmpName nm]) e b' hT3 hqq).1 $$ [HTe HTb]
    · iframe
    icases Hcs with (⟨%herr, %f, %fd, %i, %lo, %lk, %hfi, #Hlf, Hf, Hoff, Hfd, Hlks⟩ | %herr)
    rotate_left
    · -- the create failed: the segment's claim back, the deferred `RemoveAll(nm.tmp)`, the abort
      cases err
      case nil => exact absurd rfl herr
      imod segClaim_back R J (walFileName 0 0) hJ o hJs.2 CoPset.subseteq_top $$ Hsi HJr Ho
        with ⟨%hJ', %hJf, HJ⟩
      ihave Ht : tmpDirH jr (tmpName nm) hT3 $$ [HT HJ]
      · unfold tmpDirH; rw [hJs.1]; unfold tmpSub; iframe HT; iexists hJ'; iframe HJ
        rw [hJf.2 _ touch_ne_walFileName]
        isplitr
        · ipureintro; exact hJf.1
        unfold tmpEnt; iempintro
      ihave Ht := tmpDirH_any jr (tmpName nm) hT3 $$ Ht
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
      wp_apply +noauto wp_removeAllTmp wp_RmSub r (tmpName nm) R jr (e + a') hT3
        (tmpName_nameOk hnmO) $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
      · iframe; iframe #
      icases Ht with ⟨%hT4, Ht, -⟩
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
    have hino : (⟨i, false, true, lo, lk⟩ : OsFd).ino = i := rfl
    ihave Hm : osMeta (⟨i, false, true, lo, lk⟩ : OsFd).ino (DFrac.own 1) Fs.newMeta $$ [Hm]
    · rw [hino]; iexact Hm
    wp_apply (os.File.Seek.wp_end f fd _ (DFrac.own 1) (W64 0) (DFrac.own 1) (DFrac.own 1)
      (⟨i, false, true, lo, lk⟩ : OsFd) Fs.newMeta hfi.1 hnsz) $$ [$Hf $Hoff $Hfd $Hm] as %n %err ⟨Hf, Hfd, Hm, Hsk⟩
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
    ihave #Hcrct := wal.walInit_crcTable $$ Hwi
    ihave #Hmet := wal.walInit_metrics $$ Hwi
    ihave #Hseg := wal.walInit_segSize $$ Hwi
    try wp_auto
    have hwr : (⟨i, false, true, lo, lk⟩ : OsFd).writable = true := by
      rfl
    ihave Hm : osMeta (⟨i, false, true, lo, lk⟩ : OsFd).ino (DFrac.own 1) Fs.newMeta $$ [Hm]
    · rw [hino]; iexact Hm
    wp_apply wp_Prealloc f fd _ (DFrac.own 1) (DFrac.own 1) (⟨i, false, true, lo, lk⟩ : OsFd)
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
    obtain rfl : wsz = 64000000 := hwsz.2.2.1 rfl
    try wp_auto
    -- `w := &WAL{lg, dir, metadata}` (allocated), `newFileEncoder(f.File, 0)`
    irename lg => Hlgp
    irename metadata => Hmdp
    irename «$r0» => Hwal
    generalize «$r0_ptr» = wl at *
    iStructNamed Hwal
    ipersist snapBefore
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
    icases Hpa with ⟨%m2, ⟨%hm2s, %hm2maps, -, %hgrow, %hzp2⟩, Hm2, Hz2⟩
    icases (osZerosA_unfold i _ _ (DFrac.own 1)).1 $$ Hz2 with ⟨%zs2, %hzs2, Hz2⟩
    have hlo2 : m2.lo ≤ m2.size :=
      hgrow.2.1 (by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk])
    have hmaps2 : m2.maps = ∅ := by
      rw [hm2maps]; simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
    ihave Hm2 : osMeta (⟨i, false, true, lo, lk⟩ : OsFd).ino (DFrac.own 1) m2 $$ [Hm2]
    · rw [hino]; iexact Hm2
    ihave Hz2 : osBytes (⟨i, false, true, lo, lk⟩ : OsFd).ino 0 (DFrac.own 1)
        (zs2.map (fun c => ((0 : w8), c))) $$ [Hz2]
    · rw [hino, ← hnm0]; iexact Hz2
    ihave HW0 := os.fileW_start f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
      (⟨i, false, true, lo, lk⟩ : OsFd) m2 0 (zs2.map (fun c => ((0 : w8), c)))
      hlo2 (Nat.zero_le _) (by simp [hzs2, hm2s, hnm0]) $$ [Hf Hfd Hoff Hm2 Hz2]
    · iframe
    ihave #Hws := os.File.writerStreamI wp_WriteAt f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
      (⟨i, false, true, lo, lk⟩ : OsFd) m2 (zs2.map (fun c => ((0 : w8), c)))
      (createStream Mr md).length hfi.1 hwr hmaps2 (by omega) $$ Hosi
    ihave #HwsP := (io.writerStream_P _ _ _ _).1 $$ Hws
    ihave HW0' : os.fileWI f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
      (⟨i, false, true, lo, lk⟩ : OsFd) m2 (zs2.map (fun c => ((0 : w8), c))) [] $$ [HW0]
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
    have hsyncOk := os.fileWI_preSyncOk wp_Fdatasync f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1) (⟨i, false, true, lo, lk⟩ : OsFd) m2
      (zs2.map (fun c => ((0 : w8), c)))
    have hfit3 : ([] ++ ys1 ++ ys2 ++ pend2 ++
        snapFrame Mr (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) snapC0.model true).length ≤
        (createStream Mr md).length := by
      rw [hFr]
      simp only [List.length_append, List.length_nil] at hlen1 hlen2 ⊢; omega
    -- `SaveSnapshot.spec` at the state `pre` (the client model and `Sio` unused there)
    wp_apply (wp_SaveSnap R jr r wl (child r nm)
        (.pre lg mp md enc lf f (W64 0) (W64 0)
          (os.fileWI f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
            (⟨i, false, true, lo, lk⟩ : OsFd) m2 (zs2.map (fun c => ((0 : w8), c))))
          (os.fileBI f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
            (⟨i, false, true, lo, lk⟩ : OsFd) m2 (zs2.map (fun c => ((0 : w8), c))))
          (os.fileS f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) (DFrac.own 1)
            (⟨i, false, true, lo, lk⟩ : OsFd) m2 (zs2.map (fun c => ((0 : w8), c))))
          (createStream Mr md).length ([] ++ ys1 ++ ys2) pend2
          (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md))
        «$a0_ptr» snapC0.model true false true (fun _ => iprop(True)))
      $$ [Hpre Henc HW2 fp] as %serr3 ⟨%snapi', %enti', Hpre, fp, %hse3, Hr3⟩
    · dsimp only
      isplitr
      · ipureintro; exact Or.inl (by simp [snapC0, WalSnapC.model])
      isplitr
      · ipureintro; exact hfit3
      isplitr
      · ipureintro; omega
      isplitr
      · ipureintro; exact hsyncOk
      isplitr
      · ipureintro
        exact os.fileWI_preSeekOk f fd _ _ _ _ m2 _ _ (by
          have := createStream_room Mr md hMr hmd; omega)
      iframe; iframe #
    icases Hr3 with (⟨%he3, Henc, HS⟩ | ⟨%he3, %c3, %pend3, Henc, HBW⟩)
    rotate_left
    · -- `SaveSnapshot` failed: the deferred `f.Close()` and `RemoveAll(nm.tmp)`, the abort
      rcases serr3 with ei | _
      rotate_left
      · exact absurd rfl he3
      ihave Hff : (os.ownFile f fd (child (child r (tmpName nm)) (walFileName 0 0)) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (⟨i, false, true, lo, lk⟩ : OsFd)) $$ [HBW]
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
    -- `syncDir(tmpdirpath)` (F-N1): `nm.tmp` fsynced, committing `J`'s entries (all below `mJ`)
    imod osNames_next R J _ _ _ CoPset.subseteq_top $$ Hsi HJr with ⟨HJr, #HlbJr⟩
    ihave ⟨Ho, #HlbO⟩ := crOut_logLb J (walFileName 0 0) _ _ x0 s0 i $$ Ho
    ihave #HlbJ0 := osLogLb_max (hJ.restrict J ((NameSet.except []).diff [walFileName 0 0])).next
      (x0 + 1) $$ [HlbJr HlbO]
    · iframe #
    icases (osPathS_frac R r e a' jr).1 $$ Hp with ⟨Hpe, Hpa⟩
    icases (osNames_join jr (.only [tmpName nm]) e b' hT3 hqq).2 $$ HT with ⟨HTe, HTb⟩
    ihave Hpc := osPathS_child R r (tmpName nm) (DFrac.own e) jr J hT3 (tmpName_nameOk hnmO) hJs.1
      $$ Hpe HTe
    icases osCallPerm_child R r (tmpName nm) _ jr 1 $$ Hpa Hperm with ⟨Hpa, Hperm⟩
    wp_apply wp_syncDir (child r (tmpName nm)) R J (DFrac.own e) 1
      (max (hJ.restrict J ((NameSet.except []).diff [walFileName 0 0])).next (x0 + 1)) $$ [Hpc Hperm]
      as %serr4 ⟨Hpc, Hperm, Hsd⟩
    · iframe; iframe #
    icases os.osPathS_unchild R r (tmpName nm) jr J e a' (tmpName_nameOk hnmO) $$ [Hpc Hpa]
      with ⟨%hT5, Hp, HTe, %-⟩
    · iframe
    icases osCallPerm_unchild R r (tmpName nm) _ jr 1 $$ Hp Hperm with ⟨Hp, Hperm⟩
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
    imod createJ_claims R J (walFileName 0 0) hJ x0 s0 i hJs.2 (walNameP_walFileName 0 0)
      CoPset.subseteq_top $$ Hsi HJr Ho Hcm1 with ⟨%hJ', HJx, HTmps, HThv, %hJf⟩
    obtain ⟨hJlt, hJcur⟩ := hJf
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
      walTmps_not_wal (fun _ h => h) (child_ne_cleanKey r nm) $$ Hinv Hsi Hnc Hu HN HT HJx with ⟨Hnc, %hC, Hcr, HNr, HC, HJx, %hCf⟩
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
        snapFrame Mr (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) snapC0.model true = createStream Mr md := by
      rw [hFr]
      simp only [List.nil_append] at hys1 ⊢
      rw [show ys1 ++ ys2 ++ pend2 = ys1 ++ (ys2 ++ pend2) by simp, hys2, ← List.append_assoc, hys1]
    have hokS' : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS := by
      rw [← hout]; exact hokS
    -- `J`'s claim: half to the update, half kept (the handle's)
    icases (osNames_frac J (.except walTmps) (1 : Qp).half (1 : Qp).half _).1 $$ [HJx] with ⟨HJh, HJx⟩
    · rw [Qp.half_add_half]; iexact HJx
    -- the update (`createFresh_osAUnc`), its result with the invariant (`createU`)
    ihave HP : walCreateP (child r nm) (.only [nm, tmpName nm]) hC md Q Pv Wn J walTmps
        (hJ'.restrict J ((NameSet.except []).diff walTmps)) (createSeg i mS ysS) $$ [Hcr Hau Hsf HJh HmS HbS HThv]
    · unfold walCreateP createSeg
      rw [show i = (⟨i, false, true, lo, lk⟩ : OsFd).ino from rfl]
      iframe
    ihave HU : createU Mr R jr r nm hC md Q Pv Wn J (hJ'.restrict J ((NameSet.except []).diff walTmps))
        (createSeg i mS ysS) none $$ [HP]
    · unfold createU; simp only [walCreateQ]; iframe Hinv HP
      iexists _; iframe Hcm1; ipureintro; exact hJlt
    ihave Hau := createU_none Mr R jr r nm md Q Pv Wn hnW hC J hJ' i m2 mS zs2 ysS
      (max hC.next (hJ'.restrict J ((NameSet.except []).diff walTmps)).next) hin hnm hMr hmd hmdne hctmp hJjr
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) hJcoh hJcur hokS' hm2s hm2c hmaps2 $$ HU
    -- the spine law's fractions: `d` twice of the area's spine (the invariant's lend,
    -- `walInv_areaPath`: one spine stays with the pipeline) and of the new name's claim
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_areaPath walCodec Mr R jr r $$ Hinv Hnc with ⟨Hnc, %qa, Hq⟩
    iframe Hnc
    imodintro
    obtain ⟨d, a1, b1, hd1, hd2⟩ := os.qp_common qa.half (1 : Qp).half.half
    have hd : d + (d + (b1 + b1)) = (1 : Qp).half := create_qp_twice hd2
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
        (createU Mr R jr r nm hC md Q Pv Wn J (hJ'.restrict J ((NameSet.except []).diff walTmps))
          (createSeg i mS ysS))
        (createSp Mr R jr r d) (createSpR jr J nm (b1 + b1)) :=
      ⟨hin, hdl, hnmO, tmpName_nameOk hnmO, tmpName_ne nm, by simp [NameSet.Mem],
        by simp [NameSet.Mem], hctmp, hcnm,
        create_spine Mr R jr J r nm hC md Q Pv Wn _ _ _ d (b1 + b1) hd hnm hnmO,
        createU_none Mr R jr r nm md Q Pv Wn hnW hC J hJ' i m2 mS zs2 ysS _ hin hnm hMr hmd hmdne hctmp hJjr
          (Nat.le_max_left _ _) (Nat.le_max_right _ _) hJcoh hJcur hokS' hm2s hm2c hmaps2⟩
    wp_apply _wp_renameWAL R jr J r (child r nm) nm (tmpName nm) (.only [nm, tmpName nm]) hC _
      (e + a') (DFrac.own d) wl lg mp md enc lf f snapi' enti' fd _ _ _ _ _ _ _
      (createUH jr J r nm md Q Wn d) hOk ⟨hnoerr.1.mono (fun _ hp => .inl hp), by rw [← tmp_path]; exact hnoerr.2.1, hnoerr.2.2⟩
      $$ [Hp Hperm HC Hau HSp HTmps Hpre fp dirFile Henc Hf Hfd Hlks Hoff] as %w' %err Hpost
    · iframe; iframe #
      iunfold walLockIn
      iframe
    unfold renameWALPost
    icases Hpost with ⟨Hp, Hpost⟩
    icases Hpost with (⟨%herr, %x, %fp, %γ, %sz, %df, %dfd, %hfpn, HU, HSpR, Hpre, Hlk, Hfpf, Hpipe, Hmain,
        Ht1, Hdff, Hdf, Hdfd, Hsd, Hperm, Hcp⟩ | ⟨%herr, %x, %qd, %tf, %hqd, HUH, Hw, Hll2, Hpw, Hcp⟩ |
      ⟨%herr, HU, HC, Hperm, HSp, HTmps, -, Hll⟩ | ⟨%herr, %x, HU, HSpR, Hperm, Hll⟩)
    · -- committed, `w` returned: the name registered, the handle minted and assembled
      -- (`create_ghost`, `create_handleIn`: the handle before naming)
      obtain ⟨rfl, hw'⟩ := herr
      subst w'
      obtain ⟨hs1, hs2⟩ := hse3
      obtain rfl : snapi' = W64 0 := by rcases hs1 with h | h <;> rw [h] <;> rfl
      obtain rfl : enti' = W64 0 := by rcases hs2 with h | h <;> rw [h] <;> rfl
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod create_ghost Mr R jr r nm hC md Q Pv J (hJ'.restrict J ((NameSet.except []).diff walTmps))
        (createSeg i mS ysS) Wn (b1 + b1) d x wl hd $$ Hnc HU HSpR
        with ⟨Hnc, HUH, -, Hh, Hm, Hb, Ho, Htr, Hnf, #Hk⟩
      iframe Hnc
      imodintro
      icases walHandleP_openW wl (child r nm) $$ Hh with ⟨Hopen, Hpw⟩
      ihave #Hst0 := hnil
      iunfold walLockIn at Hlk
      icases Hlk with ⟨Henc, Hf, Hfd, Hlks, Hoff⟩
      have hpe0 : Fs.pageEnd 0 = 0 := by unfold Fs.pageEnd; rfl
      have hzp : ZeroPg m2 := hzp2 ⟨trivial, ⟨0, by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes,
        OsFile.ofDisk, hpe0], by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk],
        by simp [Fs.newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk, hpe0]⟩⟩
      have hoffE : W64 ((((0 + ([] ++ ys1 ++ ys2 ++ pend2 ++ snapFrame Mr
          (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) snapC0.model true).length : Nat)) : Int)) =
          W64 (((createStream Mr md).length : Nat) : Int) := by
        rw [hout, Nat.zero_add]
      have htmS := createSeg_tailMeta Mr md hMr i m2 mS zs2 ysS hokS' hm2s hm2c hmaps2 hzp
      obtain ⟨hL, hszS⟩ := createSeg_size Mr md hMr hmd i m2 mS zs2 ysS hokS' hm2s
      have hjm : ((NameSet.except []).diff walTmps).Mem (walFileName 0 0) :=
        (NameSet.mem_diff _ _ _).2 ⟨by simp [NameSet.Mem], fun h => by
          have := walTmps_not_wal _ h; rw [walNameP_walFileName] at this; cases this⟩
      have hj0 : (hJ'.restrict J ((NameSet.except []).diff walTmps)).cur !! walFileName 0 0 =
          some (.file (createSeg i mS ysS).ino) := by
        simp only [NamesH.restrict]; rw [restrictN_lookup _ _ _ hjm, hJcur]; try simp [createSeg]
      have hj1 : ∀ b n, (hJ'.restrict J ((NameSet.except []).diff walTmps)).cur !! b = some n →
          b = walFileName 0 0 := by
        intro b n hb
        simp only [NamesH.restrict] at hb
        by_cases hm : ((NameSet.except []).diff walTmps).Mem b
        · rw [restrictN_lookup _ _ _ hm, hJcur] at hb
          split at hb
          · assumption
          · cases hb
        · rw [restrictN_lookup_not _ _ _ hm] at hb; cases hb
      icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
      icases osPathS_callKey R r _ jr $$ Hp with ⟨Hp, %hkc1⟩
      ihave Hperm := osCallPerm_congr _ (hkc1 nm).symm $$ Hperm
      ihave HhIn := create_handleIn P Mr hMr wl lg r nm mp md enc lf f fd
        (child (child r (tmpName nm)) (walFileName 0 0)) (child r (tmpName nm))
        (⟨i, false, true, lo, lk⟩ : OsFd) _ (createSeg i mS ysS) jr J
        (hJ'.restrict J ((NameSet.except []).diff walTmps)) R d dfd df (child r nm) null func.nil fp γ R
        (DFrac.own d) sz rfl hwr hoffE hmp rfl htmS hL hszS hj0 hj1 hfpn
        hfi.1 rfl rfl hWR $$ [Hpre Henc Hf Hfd Hlks Hoff Htr Hm Hb HJx Hsd Hperm Hdfd Ho Hnf Hdff Hdf state decoder readClose
          Hfpf Hpipe Hmain Ht1 Hopen]
      · iframe; iframe #
      icases HhIn with ⟨%γt, HhIn⟩
      imod (receipt_zero (GF := GF)) with Hr0
      ihave Hw := walOpenWFU_intro P Mr wl (child r nm) R d f
        (createHS md i (createStream Mr md).length γt (createSeg i mS ysS).om.size)
        (createHS_done md i _ γt _) hmd $$ [HhIn Hr0]
      · iframe
      create_named_cont wl f
        (wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f fd' nmf d' $$ [Hf' Hfd' Hlks'] as %cerr' -
         · iframe; iframe #
           iunfold walLockLeft; ileft; iframe)
        (wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f (-1 : w64) nmf ⟨0, false, false, none, none⟩ $$ [Hf']
           as %cerr' -
         · iframe; iframe #
           iunfold walLockLeft; iright; iframe)
        (wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f (-1 : w64) nmf ⟨0, false, false, none, none⟩ $$ [Hf']
           as %cerr' -
         · iframe; iframe #
           iunfold walLockLeft; iright; iframe)
    · -- committed, a reopened WAL returned (the handle before naming, `walOpenWFU`, and `createUH`):
      -- the parent's fsync, the naming
      subst herr
      obtain rfl : d = qd := by cases hqd; rfl
      create_named_cont w' tf
        (wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f _ _ _ $$ [Hll2] as %cerr' -
         · iframe; iframe #)
        (wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f _ _ _ $$ [Hll2] as %cerr' -
         · iframe; iframe #)
        (wp_apply wp_lockedCloseLeft wp_Close wp_CloseC lf f _ _ _ $$ [Hll2] as %cerr' -
         · iframe; iframe #)
    · -- not committed: the unminting (`create_unmint`), the deferred `f.Close()` and
      -- `RemoveAll(nm.tmp)`, the abort over the area claim's rebuilt history (`create_abortTmpH`)
      rcases err with ei | _
      rotate_left
      · exact absurd rfl herr
      unfold createU
      icases HU with ⟨-, -, HP⟩
      simp only [walCreateQ]
      unfold walCreateP
      icases HP with ⟨Hcr, Hau, Hsf, HJh, -, -, HThv⟩
      have hfoJ : FilesOnly (hJ'.restrict J ((NameSet.except []).diff walTmps)).cur :=
        filesOnly_restrictN _ _ (fun c n hc => by
          rw [hJcur] at hc
          split at hc
          · exact ⟨i, (Option.some.inj hc).symm⟩
          · cases hc)
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod create_unmint walCodec Mr R jr r (child r nm) N h cl Wn nm hC J
        (hJ'.restrict J ((NameSet.except []).diff walTmps)) hok hnm hNnm hnmA hctmp hcnm hfoJ
        (by
          simp only [NamesH.restrict]
          by_cases hm : ((NameSet.except []).diff walTmps).Mem go!".touch"
          · rw [restrictN_lookup _ _ _ hm, hJcur, if_neg touch_ne_walFileName]
          · exact restrictN_lookup_not _ _ _ hm)
        $$ Hinv Hsi Hnc Hcr HNr HC HJh HJx HTmps HThv with ⟨Hnc, Hu, %hN, %hT', %hNcur, HN, Ht⟩
      iframe Hnc
      imodintro
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
      try wp_auto
      ihave Ht := tmpDirH_any jr (tmpName nm) hT' $$ Ht
      wp_apply +noauto wp_removeAllTmp wp_RmSub r (tmpName nm) R jr (e + a') hT'
        (tmpName_nameOk hnmO) $$ [Hp Ht Hperm] as %err' ⟨Hp, Hperm, Ht, -⟩
      · iframe; iframe #
      icases Ht with ⟨%hT4, Ht, -⟩
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod create_abortTmpH walCodec Mr R jr r N h cl nm hT4 Wn hok hnm hNnm hself hN hNcur
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
    icases HSpR with ⟨%hn, %ht, Hnm, Htmp, %hnt, -, -⟩
    try wp_auto
    wp_apply +noauto wp_RmAbs r (tmpName nm) jr R (e + a') (DFrac.own 1) ht (1 : Qp).half
      (tmpName_nameOk hnmO) hnt.2 $$ [Hp Htmp Hperm] as %err' ⟨Hp, Htmp, Hperm, -⟩
    · iframe; iframe #
    unfold createU
    icases HU with ⟨-, -, HQ⟩
    unfold walCreateQ
    icases HQ with ⟨HQ, Hsf, -, -, Hlt, -, -, Hnf, -, %s', Hpast, %hs'⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_register walCodec Mr R jr r s' (child r nm) nm Wn (b1 + b1) hn hin hnmO
      (by rw [hs']; simp) ⟨J, hnt.1⟩ $$ Hinv Hsi Hnc Hpast Hnf Hsf Hnm with ⟨Hnc, -, Hsf⟩
    imod create_areaBack walCodec Mr R jr r N h cl nm ht Wn (walLockedTok (W := W))
      walLockedTok_exclX hok hnm hself hnt.2 $$ Hinv Hsi Hnc Hlt HNr Htmp Hcl Hsf
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
