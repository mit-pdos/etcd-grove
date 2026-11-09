/-
## `schema.NewAlarmBackend(lg, be)`

**Users.** `NewServer`'s alarm store (`server.go:2425`), `applySnapshot` (`server.go:1118`). Snippet:
`examples/specreq/schema/schema.go` (`ReqAlarmPutGet`).

**Proof sketch.** Allocates `&alarmBackend{lg, be}`, read-only. **Changes.** From `specs-ref`'s
`NewAlarmBackend.lean`. **Margin.** None.
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

/-- **An `AlarmBackend` over `be`** (read-only for good). -/
def NewAlarmBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewAlarmBackend)) (Val #lg)) (Val #be))
  {{ (ab : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty) #ab); (ab ↦□ (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg be) : IProp GF) }}

end spec
end Schema
end EtcdGrove
end Perennial
