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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode backend storage go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    (wp_OpenBackend : storage.OpenBackend.spec (GF := GF) (hG := hG)) :
    storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG) := by
  intro cfg ss sn mp hk dq dq' md P D W Pk K
  wp_start as ⟨#Hss, Hmdp, Hsm, Hf, Hpo, Hpre⟩
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
    wp_apply wp_BackendPath $$ [$DataDir] as -
    wp_apply wp_Rename $$ [$Hf $Hpo] as %err2 Hr
    icases Hr with (⟨%Hr, Hf, Hpo⟩ | ⟨%Hr, Hok, Hf, Hpo⟩)
    · subst Hr
      wp_auto
      wp_apply wp_OpenBackend cfg _ P D W Pk K $$ [$Hpkg $Hf $Hpre] as %b %γ ⟨Hnew, Hncmp⟩
      iapply HΦ
      iframe Hmdp Hsm
      ileft
      isplitr
      · ipureintro; rfl
      iexists b, γ
      iframe Hnew Hncmp Hpo
      ipureintro; rfl
    · obtain ⟨ei, rfl⟩ : ∃ ei, err2 = GoInterface.ok ei := by
        cases err2 with
        | nil => exact absurd rfl Hr.1
        | ok ei => exact ⟨ei, rfl⟩
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Errorf $$ [$Hfmt $Hsl Hok] as %e -
      · simp only [EtcdGrove.fmt.argsOk]
        iframe Hok
      iapply HΦ
      iframe Hmdp Hsm
      iright
      iframe Hf Hpo
      ipureintro
      exact ⟨nofun, rfl, fun h => Hr.2 h.2⟩
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
    · simp only [EtcdGrove.fmt.argsOk]
      iframe Hok
    iapply HΦ
    iframe Hmdp Hsm
    iright
    iframe Hf Hpo
    ipureintro
    exact ⟨nofun, rfl, fun h => Herr.2 h.1⟩

end proof

end EtcdGrove
end Perennial
