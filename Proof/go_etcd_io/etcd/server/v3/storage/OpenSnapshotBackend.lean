/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/OpenSnapshotBackend.lean`. Lean-first (no Rocq
counterpart); etcd PR #22499 (branch `pr-verify/etcd-22499`), adapted from the proof of PR
#22518's version (branch `pr-verify/etcd-22518`): `syncSnapDir` is a package variable here, read
through the package fact (`storageInit`), and what it holds is proved to sync the directory
(`syncSnapDir.wp_lit`); no log line after the sync.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.syncSnapDirLit
public import Spec.go_etcd_io.etcd.server.v3.storage.OpenBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__DBFilePath
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__SnapDir
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.os.Rename

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem storage.OpenSnapshotBackend.wp_proof
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_DBFilePath : snap.Snapshotter.DBFilePath.spec (GF := GF) (hG := hG))
    (wp_Errorf : EtcdGrove.fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_BackendPath : config.ServerConfig.BackendPath.spec (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.spec (GF := GF) (hG := hG))
    (wp_SnapDir : config.ServerConfig.SnapDir.spec (GF := GF) (hG := hG))
    (wp_OpenDir : fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_Fsync : fileutil.Fsync.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_OpenBackend : storage.OpenBackend.spec (GF := GF) (hG := hG)) :
    storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG) := by
  intro cfg ss snapshot hooks dq s
  wp_start as Hsnap
  wp_auto
  iunfold ownSnapM at Hsnap
  icases Hsnap with ⟨%ds, %pm, %uf, Hsnap⟩
  iNamed Hsnap
  wp_auto
  wp_apply wp_GetIndex $$ [$Hm] as Hm
  wp_apply wp_DBFilePath as %snapPath %err Hres
  ihave Hsnap : ownSnapM snapshot dq s $$ [HD Hd HM Hm Hpb]
  · iunfold ownSnapM
    iexists ds, pm, uf
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact Hnn
    iexact Hpb
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, %Hpath⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e2 ⟨-, #He2⟩
    · fmt_args_ok
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists e2
    isplitr
    · ipureintro; rfl
    iexact He2
  subst Herr Hpath
  ipersist cfg
  ihave #cfgF : typedPointsto cfg_ptr cfg DFrac.discard $$ []
  · iexact cfg
  iStructNamedPrefix cfgF "c"
  wp_auto
  wp_apply wp_BackendPath $$ [$cDataDir] as ⟨-, %Hdir⟩
  wp_apply wp_Rename as %err Hres
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, Hpend⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e2 ⟨-, #He2⟩
    · fmt_args_ok
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists e2
    isplitr
    · ipureintro; rfl
    iexact He2
  subst Herr
  wp_auto
  wp_apply wp_SnapDir $$ [$cDataDir] as -
  -- the package variable `syncSnapDir` holds its literal, read-only (the package fact)
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hvar : storageInit (GF := GF) $$ [Hpkg]
  · iapply isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage
    iexact Hpkg
  iunfold storageInit at Hvar
  ihave #Hfn := syncSnapDir.wp_lit wp_OpenDir wp_Fsync wp_Close
  iunfold syncSnapDirFn at Hfn
  wp_auto
  wp_apply Hfn $$ [$Hpend] as %err Hres
  · ipureintro; exact Hdir
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, Hdur⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e2 ⟨-, #He2⟩
    · fmt_args_ok
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists e2
    isplitr
    · ipureintro; rfl
    iexact He2
  subst Herr
  wp_auto
  wp_apply wp_OpenBackend as %be -
  iapply HΦ
  iframe
  ileft
  iframe
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
