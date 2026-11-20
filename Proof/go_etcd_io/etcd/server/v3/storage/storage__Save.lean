/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/storage__Save.lean` (wal-link L2, 2026-11-17). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Save

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

theorem storage.storage.Save.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Save : go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (Sio := Sio) P Mr) :
    storage.storage.Save.spec (Sio := Sio) P Mr := by
  intro p ss R jr r w dir γ q hp hs sl esL es sized Q
  wp_start as ⟨#Hover, Hrd, Hw⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold storageOver at Hover
  icases Hover with ⟨#Hs, #Hguard⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold storageRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, >HP⟩
  iunfold storagePw at HP
  wp_auto
  wp_apply (wp_Save R jr r w dir γ q hp hs sl esL es sized Q) $$ [$Hw] as %err Hpost
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
