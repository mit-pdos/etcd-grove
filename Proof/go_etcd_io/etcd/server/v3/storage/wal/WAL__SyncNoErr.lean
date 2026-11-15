/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SyncNoErr.lean`: `WAL__Sync.lean`'s
proof over `sync.specNoErr`, the room kept (the flush moves the pending bytes into the tail). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SyncNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncNoErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleRoom

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.wp_proofNoErr (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.specNoErr (Sio := Sio) (W := W) P Mr := by
  intro hS0 R jr r w dir n k
  wp_start as ⟨#Harea, Hw, #Hn⟩
  icases (walOpenWFR_iff P Mr w dir k).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr, %hroom⟩
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_lenLb walCodec Mr R jr r P ⊤ CoPset.subseteq_top w dir h n TailMetaW $$ Harea Hnc Hh Hn
    with ⟨Hnc, Hh, %hn⟩
  imodintro
  iframe Hnc
  wp_auto
  wp_apply (wp_sync hS0 R jr r w dir h hD.1 (by omega)) $$ [Hh] as %err Hpost
  · iframe Harea Hh
  icases Hpost with ⟨%Herr, Hh, #Hs⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Herr
  isplitl
  · iapply (walOpenWFR_iff P Mr w dir k).2
    iexists { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
    ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
    iframe Hh Hr
    ipureintro
    refine ⟨hD, hmd, ?_⟩
    simp only [List.length_append, List.length_nil]
    omega
  · iapply (WalFs.walSyncedLb_mono (W := W) dir h.H.length n hn) $$ Hs

end proof

end EtcdGrove
end Perennial
