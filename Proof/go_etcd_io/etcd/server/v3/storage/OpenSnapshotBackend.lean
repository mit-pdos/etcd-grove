/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/OpenSnapshotBackend.lean` (D22 S-f, 2026-10-19).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__DBFilePath
public import Spec.fmt.Errorf
public import Spec.os.Rename
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath
public import Spec.go_etcd_io.etcd.server.v3.storage.OpenBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.syncDir
public import Spec.path.filepath.Dir
public import GooseLang.Ext.Fs.NoErrSpecsOpenDir
public import Proof.go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackendLemmas
-- (wal-link L2, T1) the only opener of the sealed take token
import all Proof.go_etcd_io.etcd.server.v3.storage.SnapHeld

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode backend storage go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `ServerConfig`'s `TypeRepr` from its `TypeAssumptions` (as `InvServer.lean`'s): the struct's
`IntoValTyped` is built from those of its fields, some of axiomatized types. -/
instance (priority := high) osb_serverConfig_typeRepr :
    TypeRepr go_etcd_io.etcd.server.v3.config.ServerConfig.ty
      go_etcd_io.etcd.server.v3.config.ServerConfig :=
  go.type_repr_underlying (u := go_etcd_io.etcd.server.v3.config.ServerConfig.underlying)
instance (priority := high) osb_serverConfig_typeRepr_u :
    TypeRepr go_etcd_io.etcd.server.v3.config.ServerConfig.underlying
      go_etcd_io.etcd.server.v3.config.ServerConfig :=
  go.type_repr_underlying (u := go_etcd_io.etcd.server.v3.config.ServerConfig.underlying)

theorem storage.OpenSnapshotBackend.wp_proof
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_DBFilePath : snap.Snapshotter.DBFilePath.spec (GF := GF) (hG := hG))
    (wp_Errorf : EtcdGrove.fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.spec (GF := GF) (hG := hG))
    (wp_BackendPath : config.ServerConfig.BackendPath.spec (GF := GF) (hG := hG))
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_syncDir : storage.syncDir.spec (GF := GF) (hG := hG))
    (wp_OpenBackend : storage.OpenBackend.spec (GF := GF) (hG := hG)) :
    storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG) := by
  intro _ _ cfg ss sn mp hk dq dq' md P D W Pk K γo R' hdd
  wp_start as ⟨#Hss, Hmdp, Hsm, Hhd, Hpo, Hpre⟩
  iunfold snapHeld at Hhd
  icases Hhd with ⟨Hf, HR'⟩
  ihave #Hraftpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetIndex $$ [$Hraftpb $Hsm] as Hsm
  wp_apply wp_DBFilePath $$ [$Hss $Hf] as %p %err ⟨Hf, Hp⟩
  icases Hp with (%Hp | ⟨%Herr, Hok⟩)
  · obtain ⟨rfl, rfl⟩ := Hp
    wp_auto
    ipersist cfg
    ihave #Hcf := cfg
    iStructNamed Hcf
    wp_apply (wp_BackendPath _ _ _ hdd) $$ [$DataDir] as -
    -- (S5) the rename, with no error: the file at the backend path, the snapshot's name free
    have hpar := snap.snapDBPath_parent cfg.DataDir' md.Index'
    wp_apply (wp_Rename _ _ _ _ hpar) $$ [$Hf $Hpo] as %err2 ⟨%Hr, Hf, -, Hrn⟩
    subst Hr
    wp_auto
    -- (pin e94f33b50) the snapshot directory synced after the rename, with no error (`theFs`'s
    -- `FsNoErrAll`): the rename's entry committed
    wp_apply (wp_BackendPath _ _ _ hdd) $$ [$DataDir] as -
    wp_apply wp_Dir (config.backendPathOf cfg.DataDir')
    iintro %dr %hdr
    rw [config.dirModel_backendPathOf] at hdr
    subst hdr
    rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
    · isimp only [backend.fileAt, onFs_none hfs] at Hf
      iexfalso; iexact Hf
    isimp only [backend.fileAt, onFs_some hfs, backend.fileAtF, backend.nameAtF] at Hf
    isimp only [backend.renamed, onFs_some hfs] at Hrn
    icases Hf with ⟨%i, ⟨%R, %d, %b, %dq0, %j, %qc, %h, %hp, #Hinv, #Hsh, Hp, Hcp, Hn⟩, Hfh⟩
    icases Hrn with ⟨%x, Hent, #Hlb⟩
    obtain ⟨hpath, hb, hi, hfit⟩ := hp
    have hd := snap.backendPath_dir hb hpath
    subst hd
    have hfd : Fs.PathFits (config.snapDirOf cfg.DataDir') :=
      Fs.pathFits_of_child (by rw [← hpath]; exact hfit)
    obtain ⟨Sio, hino, hpS, h1, h2⟩ := nex.ok
    have hne : Fs.FsNoErrOn (· = config.snapDirOf cfg.DataDir') := ⟨Sio, hino, h1, h2, fun p _ => hpS p⟩
    wp_apply (wp_syncDir (config.snapDirOf cfg.DataDir') R j dq0 qc (x + 1) hne hfd)
      $$ [$Hpkg $Hinv $Hsh $Hp $Hcp $Hlb] as ⟨Hp, Hcp, #Hcm⟩
    (try wp_auto)
    ihave Hdur : backend.renamedDur (snap.snapDBPath (config.snapDirOf cfg.DataDir') md.Index')
        (config.backendPathOf cfg.DataDir') $$ [Hent]
    · simp only [backend.renamedDur, onFs_some hfs]
      iexists x
      iframe Hent Hcm
    ihave Hf : backend.fileAt (config.backendPathOf cfg.DataDir') D $$ [Hp Hcp Hn Hfh]
    · simp only [backend.fileAt, onFs_some hfs, backend.fileAtF, backend.nameAtF]
      iexists i
      iframe Hfh
      iexists R, config.snapDirOf cfg.DataDir', b, dq0, j, qc, h
      iframe Hinv Hsh Hp Hcp Hn
      ipureintro; exact ⟨hpath, hb, hi, hfit⟩
    ihave Hf := backend.fileAt_fileHolds _ _ $$ Hf
    wp_apply wp_OpenBackend cfg _ P D W Pk K $$ [$Hpkg $Hf $Hpre] as %b %γ ⟨Hnew, #Hhka, #Hbf, Hpo, -⟩
    iapply HΦ
    iframe Hmdp Hsm
    ileft
    isplitr
    · ipureintro; rfl
    iexists b, γ
    iframe Hnew Hhka Hpo Hbf HR' Hdur
    ipureintro; rfl
  · obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
      cases err with
      | nil => exact absurd rfl Herr.1
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hfmt $Hsl Hok] as %e -
    · fmt_args_intro
      isplitl [Hok]
      · iapply fmt.argOkAt_of_fmtErrorOkOrNil
        isplitr
        · ipureintro; decide
        · iapply fmtErrorOkOrNil_of $$ Hok
      · itrivial
    iapply HΦ
    iframe Hmdp Hsm
    iright
    iframe Hpo
    isplitr
    · ipureintro
      exact ⟨nofun, rfl, fun h => Herr.2 h.1⟩
    iunfold snapHeld; iframe Hf HR'

end proof

end EtcdGrove
end Perennial
