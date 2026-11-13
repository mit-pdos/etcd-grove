/-
`(*filePipeline).Close()` (S/file_pipeline.go:71-74): closes `donec`, then waits on `errc` for
`run` to return (plan W2; `Proof/.../wal/Pipe.lean`). From the caller's token (alive, or dead
after an `Open` error, which gave the resources back already), the pipeline's resources
(`pipeLeft`: its half of the call permission, its path fraction, its claim). The error is `run`'s
`alloc` error if it had one not yet received, else nil; the spec says nothing of it. Lean-first.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec : Prop :=
  ∀ (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (sz : w64),
  {{ isFilePipe (GF := GF) fp γ R dir dq j sz ∗
      ((∃ n, pipeMain γ n) ∨ (∃ e, pipeDead γ e ∗ pipeLeft R dir dq j)) }}
    (App (Val (fp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.filePipeline.ty
      @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; pipeLeft R dir dq j }}

end spec

end EtcdGrove
end Perennial
