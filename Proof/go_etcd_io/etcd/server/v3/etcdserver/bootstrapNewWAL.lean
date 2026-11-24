/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapNewWAL.lean` (claim #34, stage 4,
2026-11-25): the metadata (`MustMarshalMessage.specMeta`: `walMetaEnc nodeID cid`), `wal.Create` in the
fresh WAL area (`wal.Create.specSrv`: it succeeds, the WAL opened), no `SetUnsafeNoFsync`
(`cfg.UnsafeNoFsync` false), the record. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapNewWAL
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageMeta
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IDFrac
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__WALDir
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateSrv
public import Spec.go_uber_org.zap.Logger__Panic
public import Spec.go_uber_org.zap.Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem bootstrapNewWAL.wp_proof
    (hMeta : go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specMeta (GF := GF) (hG := hG))
    (hID : membership.RaftCluster.ID.specFrac (GF := GF) (hG := hG))
    (hWALDir : config.ServerConfig.WALDir.spec (GF := GF) (hG := hG))
    (hCreate : wal.Create.specSrv (GF := GF) (hG := hG))
    (hPanic : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG)) :
    bootstrapNewWAL.spec (GF := GF) (hG := hG) := by
  intro cfg c bc dq dqc cid Hnf
  wp_start as ⟨#Hzlg, Hwp, Hc, Hcid⟩
  iunfold bootFs.walPart at Hwp
  icases Hwp with ⟨%Hwd, Hwa⟩
  ihave #Hppkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil $$ []
  · iPkgInit
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Hwpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ []
  · iPkgInit
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
  iStructNamedPrefix Hc "C"
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  try wp_auto
  -- `cl.cl.ID()`
  wp_apply (hID bc.cl' dqc cid) $$ [Hcid] as Hcid
  · iframe Hcid
  try wp_auto
  wp_apply (IntoValTyped.wp_alloc (V := go_etcd_io.etcd.api.v3.etcdserverpb.Metadata)
    (t := go_etcd_io.etcd.api.v3.etcdserverpb.Metadata.ty) _) as %ml Hml
  try wp_auto
  -- `MustMarshalMessage(&Metadata{NodeID: new(nodeID), ClusterID: new(cid)})`
  wp_apply (hMeta _ _ bc.nodeID' cid (DFrac.own 1) (DFrac.own 1)) as %md ⟨Hmd, -, -, -, -⟩
  · first
    | (ipureintro; rfl)
    | (isplitr; (· ipureintro; rfl); iframe)
    | (iframe; ipureintro; rfl)
    | trace_state
  try wp_auto
  imod ownSlice_persist md _ _ $$ Hmd with #Hmd
  -- `wal.Create(cfg.Logger, cfg.WALDir(), metadata)`
  have Hwne : cfg.DedicatedWALDir' ≠ [] := by
    rw [Hwd]; unfold srvWalDirOf; simp
  wp_apply (hWALDir cfg_ptr DFrac.discard cfg.DedicatedWALDir' Hwne) as -
  · iframe DedicatedWALDirF; try iframe #
  rw [Hwd]
  wp_apply (hCreate cfg.Logger' (srvWalDirOf cfg.DataDir') md bc.nodeID' cid) $$ [Hwa]
    as %w %err ⟨%Herr, Hopen⟩
  · iframe Hwa; try iframe #
  subst Herr
  try wp_auto
  rw [Hnf]
  try wp_auto
  iapply HΦ
  iexists (bootstrappedWAL.mk cfg.Logger' false w null slice.nil null null)
  iframe
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitl [Hopen]
  · iapply wal.bootOk_intro
    rw [Hwd]
    iexact Hopen
  iapply typedPointsto_combine _ _ _ Hcnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
