/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/OpenSnapshotBackend.lean`. Lean-first (no Rocq
counterpart); etcd PR #22518's proof (branch `pr-verify/etcd-22518`), adapted to etcd PR #22046
(branch `pr-verify/etcd-22046`): no directory sync, and the pending mark's release after the
rename, the linearization point; the error paths commit the atomic update unchanged.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.OpenBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__DBFilePath
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseDBSnapshot
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.os.Rename

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.raft.v3

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
    (wp_ReleaseDBSnapshot : snap.Snapshotter.ReleaseDBSnapshot.spec (GF := GF) (hG := hG))
    (wp_OpenBackend : storage.OpenBackend.spec (GF := GF) (hG := hG)) :
    storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG) := by
  intro cfg ss snapshot hooks dq s γ dir
  wp_start as ⟨#Hss, Hsnap⟩
  wp_auto
  iunfold ownSnapM at Hsnap
  icases Hsnap with ⟨%ds, %pm, %uf, Hsnap⟩
  iNamed Hsnap
  wp_auto
  wp_apply wp_GetIndex $$ [$Hm] as Hm
  wp_apply wp_DBFilePath $$ [$Hss] as %snapPath %err Hres
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, %Hpath⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    ihave Hsnap : ownSnapM snapshot dq s $$ [HD Hd HM Hm Hpb]
    · iunfold ownSnapM
      iexists ds, pm, uf
      simp only [named]
      iframe
      isplitr
      · ipureintro; exact Hnn
      iexact Hpb
    wp_auto
    -- the linearization point of a failure: the pending set unchanged
    simp only [LawfulSet.diff_empty]
    iapply fupd_wp
    imod HΦ with ⟨%M, Hs, Hcommit⟩
    imod Hcommit $$ %false [Hs] with HΦ
    · simp only [Bool.false_eq_true, ite_false]; iexact Hs
    imodintro
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e2 ⟨-, #He2⟩
    · fmt_args_ok
    iapply HΦ
    iframe
    simp only [Bool.false_eq_true, ite_false]
    isplitr
    · ipureintro; trivial
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
    ihave Hsnap : ownSnapM snapshot dq s $$ [HD Hd HM Hm Hpb]
    · iunfold ownSnapM
      iexists ds, pm, uf
      simp only [named]
      iframe
      isplitr
      · ipureintro; exact Hnn
      iexact Hpb
    wp_auto
    -- the linearization point of a failure: the pending set unchanged
    simp only [LawfulSet.diff_empty]
    iapply fupd_wp
    imod HΦ with ⟨%M, Hs, Hcommit⟩
    imod Hcommit $$ %false [Hs] with HΦ
    · simp only [Bool.false_eq_true, ite_false]; iexact Hs
    imodintro
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e2 ⟨-, #He2⟩
    · fmt_args_ok
    iapply HΦ
    iframe
    simp only [Bool.false_eq_true, ite_false]
    isplitr
    · ipureintro; trivial
    iexists e2
    isplitr
    · ipureintro; rfl
    iexact He2
  subst Herr
  wp_auto
  wp_apply wp_GetIndex $$ [$Hm] as Hm
  ihave Hsnap : ownSnapM snapshot dq s $$ [HD Hd HM Hm Hpb]
  · iunfold ownSnapM
    iexists ds, pm, uf
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact Hnn
    iexact Hpb
  -- the linearization point: the mark's release
  wp_apply wp_ReleaseDBSnapshot $$ [$Hss]
  imod HΦ with ⟨%M, Hs, Hcommit⟩
  imodintro
  iexists M
  iframe Hs
  iintro Hs
  imod Hcommit $$ %true [Hs] with HΦ
  · simp only [ite_true]; iexact Hs
  imodintro
  iintro -
  wp_auto
  wp_apply wp_OpenBackend as %be -
  iapply HΦ
  iframe
  simp only [ite_true]
  iframe

end proof

end EtcdGrove
end Perennial
