/-
## `schema.NewAuthBackend(lg, be)`

**Users.** `NewServer` (`server.go:369`), `applySnapshot` (`server.go:1127`). Snippet:
`examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** Allocates `&authBackend{be, lg}`, made read-only (never written).

**Changes.** From `specs-ref`'s `NewAuthBackend.lean` (the real backend, the old auth tokens): the
struct only; what its methods do is over the backend's triples. **Margin.** None.
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

/-- **An `AuthBackend` over `be`** (read-only for good). -/
def NewAuthBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend)) (Val #lg)) (Val #be))
  {{ (abe : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) #abe); (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) }}

end spec
end Schema
end EtcdGrove
end Perennial
