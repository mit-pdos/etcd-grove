/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/storage__SaveSnap.lean` (wal-link L2, 2026-11-17). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.storage__SaveSnap

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode storage go_etcd_io.raft.v3
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

theorem storage.storage.SaveSnap.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_SaveSnapshot : go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (Sio := Sio) P Mr) :
    storage.storage.SaveSnap.spec (Sio := Sio) P Mr := by
  intro p ss R jr r w dir γ q sn mp dq m sized Q
  wp_start as ⟨#Hover, Hrd, HM, #Hmeta, %Hset, %Henc, #Harea, Hws, %Hcov, %Hidx, %Hlt, %Hlen, HAU⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold storageOver at Hover
  icases Hover with ⟨#Hs, #Hguard⟩
  iunfold metaRoC at Hmeta
  icases Hmeta with ⟨%pc, %pi, %pt, %Hmnn, #HC, #Hc, #HI, #Hi, #HT, #Ht, -⟩
  obtain ⟨hi, ht⟩ := Hset
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hi
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 ht
  simp only [hi, ht, optCell]
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold storageRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, >HP⟩
  iunfold storagePw at HP
  (try wp_auto)
  wp_apply wp_SnapshotMetadata_GetConfState_fieldS mp pc DFrac.discard Hmnn $$ [$HC] as -
  (try wp_auto)
  imod walSnapAt_storageLit Mr m walsnap_ptr pi pt pc i t _ _ hi ht Henc $$ [walsnap] [] [] [] with #Hsnap
  · iexact walsnap
  · iexact Hi
  · iexact Ht
  · iexact Hc
  wp_apply (wp_SaveSnapshot R jr r w dir (.shared γ q) walsnap_ptr m.model m.confState.isSome sized Q)
    $$ [Hws HAU] as %err Hpost
  · dsimp only
    iframe Hws HAU Harea Hsnap
    ipureintro; exact ⟨Hcov, Hidx, Hlt, Hlen⟩
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP]
  · inext; iunfold storagePw; iexact HP
  iintro Hrd
  wp_auto
  iapply HΦ
  iunfold storageRd
  iframe

end proof

end EtcdGrove
end Perennial
