/-
## `schema.NewMembershipBackend(lg, be)`

**Users.** Bootstrap (`bootstrap.go:133,512`), `applySnapshot` (`server.go:1132`: `SetBackend`).
Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Proof sketch.** Allocates `&membershipBackend{lg, be}`, read-only. **Changes.** From `specs-ref`'s
`NewMembershipBackend.lean`. **Margin.** None.
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

/-- **A membership backend over `be`** (read-only for good). -/
def NewMembershipBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewMembershipBackend)) (Val #lg)) (Val #be))
  {{ (mb : Loc), RET #mb; (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) }}

end spec
end Schema
end EtcdGrove
end Perennial
