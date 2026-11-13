/-
`(*filePipeline).run()` (S/file_pipeline.go:94-110), the pipeline's goroutine: from its state at
round 0 (`pipeRun`), it allocates file after file, offering each on `filec` (the indexed handshake:
the file `n` for the claim on `pipeTmp (n + 1)`) until `donec` closes (the file in hand removed and
closed) or an `alloc` fails (the error sent on `errc`); it closes `errc` on return, with its
resources (`pipeLeft`) in the error or, after `donec`, in the close. Lean-first (plan W2).
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.spec : Prop :=
  ∀ (fp : Loc) (γ : PipeNames) (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (sz : w64),
  {{ isFilePipe (GF := GF) fp γ R dir dq j sz ∗ pipeRun fp γ R dir dq j 0 }}
    (App (Val (fp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.filePipeline.ty
      @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
