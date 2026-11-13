/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/openWALFiles.lean` (W5 of
`notes/wal-fsext-plan.md`; `sorry`: the callees `fileutil.TryLockFile`, `fileutil.NewFileReader`, `filepath.Join`, `closeAll` have no spec yet).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
