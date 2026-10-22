/-
`(*fifo).run` (`schedule.go`), the scheduler's worker goroutine. Lean-first (2026-10-22, the
scheduler translated with its body).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- **`f.run()`**, the worker, with its resources (`workerRes`: the run token, its thread token
among them): it runs the pending jobs in order until the scheduler is stopped, then the rest with
the cancelled context, closes `f.donec` and `f.resume` and returns its thread token. -/
abbrev schedule.fifo.run.spec : Prop :=
  ∀ (l : Loc) (γ : schedule.SchedNames) (F : schedule.FifoNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.fifoIs l γ F ∗ schedule.workerRes γ F }}
    (App (Val (l @!! go.GoType.PointerType schedule.fifo.ty @!! go!"run")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
