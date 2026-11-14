/-
`newFilePipeline(lg, dir, fileSize)` (S/file_pipeline.go:43-58): the pipeline struct, its three
channels (`filec` unbuffered, `errc` of capacity 1, `donec` unbuffered), and its goroutine `run`
started. The caller gives the pipeline half of the call permission, a fraction of the directory's
path and the whole claim on `0.tmp` (`pipeTmp 0`); it keeps the claim on `1.tmp` (`pipeTmp 1`, the
first `Open`'s `pipeQ j 0`) and gets the token `pipeMain γ 0`. `lg` non-nil (`zapLoggerOk`; the
`zap.NewNop()` branch not taken); `dir` shorter than `2^61` (`filepath.Join`'s premise). Lean-first (plan W2).
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec : Prop :=
  ∀ (lg : Loc) (dir : GoString) (sz : w64) (R : Roots) (dq : DFrac) (j : Ino),
  0 ≤ sz.toInt → sz.toInt ≤ 0xffffffff000 → dir.length < 2 ^ 61 → sz.toInt % 8 = 0 →
  {{ zapLoggerOk (GF := GF) lg ∗ osInv (GF := GF) ∗ osSharedInv R ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      pipeRes R dir dq j ∗ tmpClaim j (pipeTmp 0) }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline)) (Val #lg))
      (Val #dir)) (Val #sz))
  {{ (fp : Loc), RET #fp; ⌜fp ≠ null⌝ ∗ ∃ γ : PipeNames, isFilePipe fp γ R dir dq j sz ∗ pipeMain γ 0 }}

end spec

end EtcdGrove
end Perennial
