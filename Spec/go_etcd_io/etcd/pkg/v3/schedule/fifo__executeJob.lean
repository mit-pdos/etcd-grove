/-
`(*fifo).executeJob(todo, updatedFinishedStats)` (`schedule.go`): runs the head job, then (when
`!updatedFinishedStats`) pops it and broadcasts; a panic inside the job is re-raised through
`lg.Panic` (unreachable: the job's contract excludes panics). Internal.

**Proof sketch**: `jobOk`'s `Do` with `schedCtx`, the job's pre from `fifoHead`; the deferred pop
deposits its post where the next job (or `donec`) takes it.
**Changes**: restated over `fifoHead`. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Api

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

def fifo.executeJob.spec : Prop :=
  ∀ (l : Loc) (γ : SchedNames) (Pay : IProp GF) (j : GoInterface) (upd : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ isFifo l γ Pay ∗
      fifoWorker l γ ∗ fifoHead l γ j }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.schedule.fifo.ty @!!
      go!"executeJob")) (Val #j)) (Val #upd))
  {{ RET #(); fifoWorker l γ }}

end spec
end Schedule
end EtcdGrove
end Perennial
