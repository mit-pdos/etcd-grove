/-
`job.Name()` (`schedule.go`): internal (`executeJob`'s panic message). Returns the name field.
**Changes**: unchanged. **Margin**: none.
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

def job.Name.spec : Prop :=
  ∀ (jv : go_etcd_io.etcd.pkg.v3.schedule.job),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule }}
    (App (Val (jv @!! go_etcd_io.etcd.pkg.v3.schedule.job.ty @!! go!"Name")) (Val #()))
  {{ RET #jv.name'; True }}

end spec
end Schedule
end EtcdGrove
end Perennial
