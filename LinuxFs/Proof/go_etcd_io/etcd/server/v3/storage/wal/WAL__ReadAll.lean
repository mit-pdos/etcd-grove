/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` (W3/W5 of
`notes/wal-fsext-plan.md`; `sorry`: the plan's W3/W5 log says what is missing).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReadAll

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

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.wp_proof (P : WalPbIn GF) (Mr : WalMarshal) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.spec (W := W) P Mr := by
  sorry

end proof

end EtcdGrove
end Perennial
