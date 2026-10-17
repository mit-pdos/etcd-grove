/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean`.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046` only). The two
success paths (the file already there, or renamed into place) commit the atomic update at
`markPendingDB`, after the directory sync; every error path commits it unchanged before
returning.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__SaveDBFrom
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__markPendingDB
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__dbFilePath
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.fsyncSnapDir
public import Spec.os.CreateTemp
public import Spec.os.File__Name
public import Spec.os.File__Close
public import Spec.os.Remove
public import Spec.os.Rename
public import Spec.io.Copy
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import Spec.time.Duration__Seconds
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Error
public import Perennial.Proof.time.Link
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.Snapshotter.SaveDBFrom.wp_proof
    (wp_markPendingDB : snap.Snapshotter.markPendingDB.spec (GF := GF) (hG := hG))
    (wp_dbFilePath : snap.Snapshotter.dbFilePath.spec (GF := GF) (hG := hG))
    (wp_fsyncSnapDir : snap.fsyncSnapDir.spec (GF := GF) (hG := hG))
    (wp_CreateTemp : os.CreateTemp.spec (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.spec (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.spec (GF := GF) (hG := hG))
    (wp_Copy : io.Copy.spec (GF := GF) (hG := hG))
    (wp_Fsync : fileutil.Fsync.spec (GF := GF) (hG := hG))
    (wp_Exist : fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_Bytes : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_ZError : zap.Error.spec (GF := GF) (hG := hG)) :
    snap.Snapshotter.SaveDBFrom.spec (GF := GF) (hG := hG) := by
  intro s γ dir r id
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_start as ⟨#Hs, Hr⟩
  ihave #Hs' := Hs
  iunfold isSnapshotter at Hs'
  icases Hs' with ⟨%mref, %lg, #Hm, #Hlg, %Hlgnn, #Hdir, #Hfs, #Hmu⟩
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.snap.snapInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.snap.snapInit at Hinit
  icases Hinit with ⟨⟨%hf, #Hhf, #Hhfs⟩, ⟨%hs, #Hhs, #Hhss⟩⟩
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.histSpec at Hhfs Hhss
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply time.wp_Now as %start -
  (try wp_auto)
  wp_apply wp_CreateTemp as %f %err Hres
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, %p, Hfh, #Hfn, Hrmp⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    simp only [LawfulSet.diff_empty]
    iapply fupd_wp
    imod HΦ with ⟨%M, HM, Hc⟩
    imod Hc $$ %false [HM] with HΦ
    · simp only [Bool.false_eq_true, ite_false]; iexact HM
    imodintro
    (try wp_auto)
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    iexists e
    iframe #
    ipureintro; rfl
  subst Herr
  (try wp_auto)
  wp_apply wp_Copy $$ [$Hr] as %n %cerr Hres
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · -- the copy failed: close, remove the temporary file
    subst Herr
    (try wp_auto)
    wp_apply wp_Close $$ [$Hfh] as %cl -
    (try wp_auto)
    wp_apply wp_Name $$ [$Hfn]
    simp only [LawfulSet.diff_empty]
    iapply fupd_wp
    imod HΦ with ⟨%M, HM, Hc⟩
    imod Hc $$ %false [HM] with HΦ
    · simp only [Bool.false_eq_true, ite_false]; iexact HM
    imodintro
    wp_apply wp_Remove $$ [$Hrmp] as %re -
    (try wp_auto)
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    iexists _
    iframe #
    ipureintro; rfl
  subst Herr
  (try wp_auto)
  wp_apply time.wp_Now as %t1 -
  (try wp_auto)
  wp_apply wp_Fsync $$ [$Hfh] as %fe ⟨Hfh, Hres⟩
  (try wp_auto)
  wp_apply time.wp_Since as %d1 -
  wp_pures
  wp_apply wp_Seconds as %sec1 -
  (try wp_auto)
  wp_apply Hhfs
  (try wp_auto)
  wp_apply wp_Close $$ [$Hfh] as %cl -
  (try wp_auto)
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · -- the fsync failed
    subst Herr
    (try wp_auto)
    wp_apply wp_Name $$ [$Hfn]
    simp only [LawfulSet.diff_empty]
    iapply fupd_wp
    imod HΦ with ⟨%M, HM, Hc⟩
    imod Hc $$ %false [HM] with HΦ
    · simp only [Bool.false_eq_true, ite_false]; iexact HM
    imodintro
    wp_apply wp_Remove $$ [$Hrmp] as %re -
    (try wp_auto)
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    iexists _
    iframe #
    ipureintro; rfl
  subst Herr
  (try wp_auto)
  wp_apply wp_dbFilePath $$ [$Hs]
  (try wp_auto)
  wp_apply wp_Exist as %ex -
  wp_if_destruct
  · -- rename the temporary file into place, sync the directory
    (try wp_auto)
    wp_apply wp_Name $$ [$Hfn]
    wp_apply wp_Rename as %rne Hres
    iunfold fsResult at Hres
    icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
    rotate_left
    · subst Herr
      (try wp_auto)
      wp_apply wp_Name $$ [$Hfn]
      simp only [LawfulSet.diff_empty]
      iapply fupd_wp
      imod HΦ with ⟨%M, HM, Hc⟩
      imod Hc $$ %false [HM] with HΦ
      · simp only [Bool.false_eq_true, ite_false]; iexact HM
      imodintro
      wp_apply wp_Remove $$ [$Hrmp] as %re -
      (try wp_auto)
      iapply HΦ
      simp only [Bool.false_eq_true, ite_false]
      iexists _
      iframe #
      ipureintro; rfl
    subst Herr
    (try wp_auto)
    wp_apply wp_fsyncSnapDir as %de Hres
    iunfold fsResult at Hres
    icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
    rotate_left
    · subst Herr
      simp only [LawfulSet.diff_empty]
      iapply fupd_wp
      imod HΦ with ⟨%M, HM, Hc⟩
      imod Hc $$ %false [HM] with HΦ
      · simp only [Bool.false_eq_true, ite_false]; iexact HM
      imodintro
      (try wp_auto)
      wp_apply wp_String as %f1 -
      wp_apply wp_ZError as %f2 -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨Hfsl, -⟩
      (try wp_auto)
      wp_apply wp_Warn
      · ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      simp only [Bool.false_eq_true, ite_false]
      iexists _
      iframe #
      ipureintro; rfl
    subst Herr
    (try wp_auto)
    -- the linearization point: the mark
    wp_apply wp_markPendingDB $$ [$Hs]
    simp only [LawfulSet.diff_empty]
    imod HΦ with ⟨%M, HM, Hc⟩
    imodintro
    iexists M
    iframe HM
    iintro HM
    imod Hc $$ %true [HM] with HΦ
    · simp only [ite_true]; iexact HM
    imodintro
    iintro -
    (try wp_auto)
    wp_apply wp_String as %f1 -
    wp_apply wp_Int64 as %f2 -
    wp_apply wp_Bytes as %hb -
    wp_apply wp_String as %f3 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    (try wp_auto)
    wp_apply wp_Info
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply time.wp_Since as %d2 -
    (try wp_auto)
    wp_apply wp_Seconds as %sec2 -
    (try wp_auto)
    wp_apply Hhss
    (try wp_auto)
    iapply HΦ
    simp only [ite_true]
    ipureintro; trivial
  · -- the file is already there: drop the temporary one, sync the directory
    (try wp_auto)
    wp_apply wp_Name $$ [$Hfn]
    wp_apply wp_Remove $$ [$Hrmp] as %re -
    (try wp_auto)
    wp_apply wp_fsyncSnapDir as %de Hres
    iunfold fsResult at Hres
    icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
    rotate_left
    · subst Herr
      simp only [LawfulSet.diff_empty]
      iapply fupd_wp
      imod HΦ with ⟨%M, HM, Hc⟩
      imod Hc $$ %false [HM] with HΦ
      · simp only [Bool.false_eq_true, ite_false]; iexact HM
      imodintro
      (try wp_auto)
      iapply HΦ
      simp only [Bool.false_eq_true, ite_false]
      iexists _
      iframe #
      ipureintro; rfl
    subst Herr
    (try wp_auto)
    -- the linearization point: the mark
    wp_apply wp_markPendingDB $$ [$Hs]
    simp only [LawfulSet.diff_empty]
    imod HΦ with ⟨%M, HM, Hc⟩
    imodintro
    iexists M
    iframe HM
    iintro HM
    imod Hc $$ %true [HM] with HΦ
    · simp only [ite_true]; iexact HM
    imodintro
    iintro -
    (try wp_auto)
    iapply HΦ
    simp only [ite_true]
    ipureintro; trivial

end proof

end EtcdGrove
end Perennial
