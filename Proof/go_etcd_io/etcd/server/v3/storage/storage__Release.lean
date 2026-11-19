/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/storage__Release.lean` with the body of
`(*storage.storage).Release` (wal-link L2 as `wp_proofNext`, 2026-11-17; the spec in place at L3,
2026-11-18, the axiom `storage.storage.Release.wp_proof` removed). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Release
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode storage go_etcd_io.raft.v3 snap
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the spec's docstring. -/
theorem storage.storage.Release.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_ReleaseLockTo : go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (Sio := Sio) P Mr)
    (wp_ReleaseSnapDBs : snap.Snapshotter.ReleaseSnapDBs.spec (GF := GF) (hG := hG)) :
    storage.storage.Release.spec (Sio := Sio) P Mr := by
  intro p ss R jr r w dir γ q sn mp dq dq' md γd img Rm t i n cs Q
  wp_start as ⟨#Hover, Hrd, #Hss, HM, Hsm, #Hinv, #HRm, #Harea, Hws, #Hsyn, HAU⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hsnp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap $$ []
  · iPkgInit
  iunfold storageOver at Hover
  icases Hover with ⟨#Hs, #Hguard⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold storageRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, >HP⟩
  iunfold storagePw at HP
  (try wp_auto)
  wp_apply wp_GetIndex $$ [$Hrpb $Hsm] as Hsm
  (try wp_auto)
  wp_apply (wp_ReleaseLockTo R jr r w dir γ q md.Index' t i n cs Q) $$ [$Harea $Hws $Hsyn $HAU]
    as %err ⟨%Herr, Hws, HQ⟩
  subst Herr
  (try wp_auto)
  wp_apply (wp_ReleaseSnapDBs ss sn mp dq dq' md γd img Rm) $$ [$Hsnp $Hss $HM $Hsm $Hinv $HRm]
    as %err ⟨HM, Hsm, %Herr⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP]
  · inext; iunfold storagePw; iexact HP
  iintro Hrd
  wp_auto
  iapply HΦ
  iunfold storageRd
  iframe
  ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
