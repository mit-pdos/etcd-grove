/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/filePipeline__run.lean`.
**Unfinished (`sorry`).** Plan (`wp_with_defer`, `wp_for` with `∃ n, pipeRun fp γ R dir dq j n`):
* `alloc` (`wp_alloc`): an error → `wp_spsc_send` of `pipeErrP` (`pipeLeft`: `pipeRes` and the claim
  on `pipeTmp n`, `pipeTmp_mem`), return; the deferred `close(errc)` with `pipeErrR [e]` (its left
  disjunct);
* the file → the `select` (`chan.wp_select_blocking`): the send on `filec` by `hsn_send_au`
  (`hsnSnd n`, `pipeFile n`) gives `hsnSnd (n + 1)` and `pipeQ j n` (the claim on
  `pipeTmp (n + 1)` and `n + 1 < 2^63`): `pipeRun (n + 1)`, the loop goes on; `donec`'s receive
  (`broadcast_chan_receive`, `.Unknown`) gives `pipeClosedW`: `os.Remove(f.Name())`
  (`os.Remove.specFileS` with the claim split `½ + ½`, a trivial `osAU` by `aupd_intro`; the claim
  after the outcome is a `tmpClaim`: the name absent, or still the file), `f.Close()` (the
  promoted `(*os.File).Close`), return; the deferred close with `pipeErrR []` (`pipeLeft` and
  `pipeClosedW`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__run
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__alloc
public import LinuxFs.Spec.os.Remove
public import LinuxFs.Spec.os.File__Name
public import LinuxFs.Spec.os.File__Close

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

theorem go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.wp_proof
    (_wp_alloc : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.spec (GF := GF) (hG := hG))
    (_wp_Remove : os.Remove.specFileS (GF := GF) (hG := hG))
    (_wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (_wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
