/-
`job.Do(ctx)` (`schedule.go`): calls the closure. Internal (`jobOk`'s realization for `NewJob`'s
jobs; `executeJob` calls `Do` through the `Job` interface).
**Changes**: restated over `funcOk`. **Margin**: none.
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

def job.Do.spec : Prop :=
  ∀ (jv : go_etcd_io.etcd.pkg.v3.schedule.job) (ctx : GoInterface) (Pay P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      funcOk jv.do' Pay P Q ∗ schedCtx ctx Pay ∗ P }}
    (App (Val (jv @!! go_etcd_io.etcd.pkg.v3.schedule.job.ty @!! go!"Do")) (Val #ctx))
  {{ RET #(); Q }}

end spec
end Schedule
end EtcdGrove
end Perennial
