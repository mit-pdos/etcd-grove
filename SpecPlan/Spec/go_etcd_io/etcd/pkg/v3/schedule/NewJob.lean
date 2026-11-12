/-
`schedule.NewJob(name, do)` (`schedule.go`).

**Users**: `server.go:841` (`run`: `NewJob("server_applyAll", func(context.Context) { s.applyAll(&ep,
&ap) })`), `kvstore.go:147, 201, 236` (mvcc's compaction and barrier jobs). Snippet `ReqFifoChain`.

**Proof sketch**: the `job` value `{name, do}` boxed as a `Job` interface; its `Do` is
`job.Do.spec`, which calls `do` under `funcOk`.

**Changes**: restated over `funcOk`/`jobOk` (was `jobIs γ j Pre Prev Post` over saved names).

**Margin**: the name is not modelled (`job.Name.spec` returns it).
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

/-- **A job** from a closure: its `Do` is the closure's contract. -/
def NewJob.spec : Prop :=
  ∀ (name : GoString) (f : GoFunc) (Pay P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ funcOk f Pay P Q }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.schedule.NewJob)) (Val #name)) (Val #f))
  {{ (j : GoInterface), RET #j; jobOk j Pay P Q }}

end spec
end Schedule
end EtcdGrove
end Perennial
