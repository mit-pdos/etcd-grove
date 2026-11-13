/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/filePipeline__alloc.lean`.
**Unfinished (`sorry`).** Plan: `fmt.wp_SprintfTmp` (`decimal (n % 2) ++ ".tmp" = pipeTmp n`,
`n < 2^63`), `filepath.Join` (no spec yet), `createNewWALFile.specLocked` at `forceNew = true` over
the open triple of the claim (`os.OpenFile.specCreateTruncSnc` when the name is absent, a trivial
atomic update since the pipeline holds the whole claim; `os.OpenFile.wp_truncS` when it holds a
file), the field load `lf.File` (`fileutil.lockedFile`), `fileutil.Preallocate.spec` (`ext`, from
size 0: `preGrown i m sz` is `osMeta` of size `sz` and `osZerosA i 0 sz`), the error path's
`zap` logging and the promoted `(*os.File).Close`.
**Gaps found:** (1) the open specs' post (`fileutil.openPost`, and so `lockPost`) gives no
`os.ownOff f 0`, which `Preallocate` and the cut's encoder (`newFileEncoder`, `Seek`) need: the
open specs should return the offset field (their models allocate it at 0); (2) `m.maps = ∅` of the
truncated file (`trFile` gives `mcellsAny m.maps`); (3) `filepath.Join`'s spec.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__alloc
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate

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

theorem go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.wp_proof
    (_wp_create : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF)
      (hG := hG))
    (_wp_Preallocate : go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
