/-
`osCallPerm_join'` and `pipeTmp_mem`, out of `WAL__Close.lean`'s proof so that `WAL__CloseNoErr.lean` imports
them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Close
public import Spec.os.File__Close
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseAu
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem osCallPerm_join' :
    osCallPerm (L := hG.goose_localGS) (1 : Qp).half.half ∗
      osCallPerm (L := hG.goose_localGS) (1 : Qp).half.half ⊢
      osCallPerm (L := hG.goose_localGS) (1 : Qp).half := by
  have h := osCallPerm_split (L := hG.goose_localGS) (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.2

theorem pipeTmp_mem (n : Nat) : pipeTmp n ∈ walTmps := by
  unfold pipeTmp walTmps; split <;> simp

end proof

end EtcdGrove
end Perennial
