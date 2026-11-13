/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/newFilePipeline.lean`.
**Unfinished (`sorry`).** Plan: `chan.wp_make1` (`filec`, `donec`) and `wp_make2` (`errc`, capacity
1: `Buffered []`); `start_hsn` (`filec`), `start_spsc` (`errc`), `alloc_broadcast_chan` (`donec`,
`pipeClosedW`), `dghostVar_alloc false` (the alive flag); the composite literal's points-to split
by fields (`iStructNamed`), all but `count` made persistent; `Fork` of `run` with
`pipeRun fp γ R dir dq j 0` (`run.wp_proof`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.wp_proof
    (_wp_run : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
