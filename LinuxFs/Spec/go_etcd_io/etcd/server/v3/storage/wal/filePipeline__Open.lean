/-
`(*filePipeline).Open()` (S/file_pipeline.go:62-69): the next file from `filec`, or `run`'s
`alloc` error from `errc` (plan W2; `Proof/.../wal/Pipe.lean`). The caller's `n`-th call hands
back the claim on `pipeTmp (n + 1)` (`pipeQ`) and gets the file `n` (`pipeFile`); on an error the
pipeline is dead (`pipeDead`), its resources back (`pipeLeft`), the claim kept. `errc` closed and
empty cannot be met: only `Close` lets `run` close it without a value. Lean-first.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Open.spec : Prop :=
  ∀ (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (sz : w64)
    (n : Nat),
  {{ isFilePipe (GF := GF) fp γ R dir dq j sz ∗ pipeMain γ n ∗ pipeQ j n }}
    (App (Val (fp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.filePipeline.ty
      @!! go!"Open")) (Val #()))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
      (⌜err = interface.nil⌝ ∗ pipeMain γ (n + 1) ∗ pipeFile j dir n lf) ∨
      (⌜err ≠ interface.nil ∧ lf = null⌝ ∗ pipeDead γ err ∗ pipeLeft R dir dq j ∗ pipeQ j n) }}

end spec

end EtcdGrove
end Perennial
