/-
## `(*alarmBackend).ForceCommit()`: assumed (names only)

**Users.** The alarm store (2e: `NewAlarmStore` creates the bucket and reads every alarm;
`Activate`/`Deactivate` put and delete on the apply thread; `Recover`). Snippet: `examples/specreq/schema/schema.go`
(`ReqAlarmPutGet`).

**Assumed** (`alarm.go`): `be.ForceCommit()`: the backend's commit runs its hooks under its own lock invariant. The bucket's records are as `alarmBkt` says (its realization in the
API's header).

**Changes.** New (the old alarm store's backend calls were inside its trusted specs).
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Commits** (the backend's commit and its hooks). -/
def alarmBackend.ForceCommit.spec : Prop :=
  ∀ (ab lg : Loc) (be : GoInterface) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (ab ↦□ (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg be) : IProp GF) ∗ True }}
    (App (Val (ab @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"ForceCommit")) (Val #()))
  {{ RET #(); True }}

end spec
end Schema
end EtcdGrove
end Perennial
