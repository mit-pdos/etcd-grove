/-
`(*filePipeline).alloc()` (S/file_pipeline.go:76-92, with the fork's `O_TRUNC`): the file
`pipeTmp n` (`n = fp.count`) of the pipeline's directory, created or truncated
(`createNewWALFile(fpath, true)`, locked), preallocated to `fp.size` zeros; `fp.count` incremented.
From the whole claim on the name (`tmpClaim`) and the pipeline's resources (`pipeRes`): on success
the file (`pipeFile`: the claim now holding it); on an error the claim back (the name absent or
holding some file: a preallocation error closes the created file and leaves it). `n < 2^63`: the
signed `count % 2` is `n % 2`. Lean-first (plan W2).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Pipe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.spec : Prop :=
  ∀ (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (sz : w64)
    (n : Nat),
  n < 2 ^ 63 →
  {{ isFilePipe (GF := GF) fp γ R dir dq j sz ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"count" fp ↦ W64 n ∗
      tmpClaim j (pipeTmp n) ∗ pipeRes R dir dq j }}
    (App (Val (fp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.filePipeline.ty
      @!! go!"alloc")) (Val #()))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); pipeRes R dir dq j ∗
      ((⌜err = interface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"count" fp ↦
            W64 (n + 1) ∗ pipeFile j dir n lf) ∨
       (⌜err ≠ interface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.filePipeline go!"count" fp ↦ W64 n ∗
          tmpClaim j (pipeTmp n))) }}

end spec

end EtcdGrove
end Perennial
