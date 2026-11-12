/-
`(*fifo).run()` (`schedule.go`): the worker goroutine (internal; forked by `NewFIFOScheduler`).

**Proof sketch**: loop: under the lock, take the head job's resources (`fifoHead`) if any, and run it
(`executeJob(todo, false)`, which pops it); else wait on `resume` or the context's `Done`; once done,
take the remaining pendings out of the invariant and run each (`executeJob(todo, true)`); the
deferred close of `donec` carries the last job's post. Internal: mirrors the code.
**Changes**: restated over `fifoWorker`/`fifoHead`. **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.schedule.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schedule

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

def fifo.run.spec : Prop :=
  ∀ (l : Loc) (γ : SchedNames) (Pay : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ isFifo l γ Pay ∗
      fifoWorker l γ }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.schedule.fifo.ty @!!
      go!"run")) (Val #()))
  {{ RET #(); True }}

end spec
end Schedule
end EtcdGrove
end Perennial
