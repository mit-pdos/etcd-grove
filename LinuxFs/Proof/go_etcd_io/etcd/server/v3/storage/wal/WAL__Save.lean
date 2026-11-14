/-
`(*WAL).Save` over its callees: `sync`, `saveEntry`, `saveState`, `cut` (W2's, a hypothesis until W2 proves it). Also to come as hypotheses: `raft.IsEmptyHardState`/`MustSync` over `P.hsIn`, `Seek`. Proved over the callees' specs (`sorry` while W6 is in progress). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveState
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws

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

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_saveEntry : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (W := W) P Mr)
    (wp_saveState : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (wp_cut : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (W := W) P Mr := by
  intro R jr r w dir hp hs sl esL es sized Q
  wp_start as ⟨#Harea, Hw, #Hhs, #Hsl, Hes, %hidx, %hsz, Hau⟩
  icases (walOpenWF_iff P Mr w dir).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr⟩
  ihave %hS := walAreaOk_encState walCodec Mr R jr r $$ Harea
  -- the commit, before the call's first step
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_append P Mr R jr r w dir h (WalOpG.save hs es).toRaw sized Q hD.1
    (saveOp_fit Mr hs es (hS hs) hsz) (fun a b => saveOp_idx Mr h.H hs es _ _ a b)
    $$ Harea Hnc Hh Hau with ⟨Hnc, Hh, #Hlb, HQ, %hcp⟩
  imodintro
  iframe Hnc
  sorry

end proof

end EtcdGrove
end Perennial
