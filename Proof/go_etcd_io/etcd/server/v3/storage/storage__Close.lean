/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/storage__Close.lean` (wal-link L2, 2026-11-17). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Close

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

theorem storage.storage.Close.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Close : go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (Sio := Sio) P Mr) :
    storage.storage.Close.spec (Sio := Sio) P Mr := by
  intro p ss R jr r w dir γ Q
  wp_start as ⟨#Hover, Hw⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold storageOver at Hover
  icases Hover with ⟨#Hs, #Hguard⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hrl, >HP⟩
  iunfold storagePw at HP
  wp_auto
  wp_apply (wp_Close R jr r w dir (.shared γ) Q) $$ [$Hw] as %err Hpost
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hrl HP]
  · inext; iunfold storagePw; iexact HP
  iapply HΦ
  iexact Hpost

end proof

end EtcdGrove
end Perennial
