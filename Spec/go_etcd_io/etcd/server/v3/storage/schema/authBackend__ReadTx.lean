/-
## `(*authBackend).ReadTx()`

**Users.** The auth store (`auth/store.go`: `as.be.ReadTx()`), `GetUser` and the other getters.
Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `abe.be.ReadTx()` (`retOk`: the backend's fixed transaction), a fresh
`&authReadTx{tx, lg}`, read-only. **Changes.** From `specs-ref`'s `authBackend__ReadTx.lean` where there was
one. **Margin.** None.
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

/-- **An `AuthReadTx` over the backend's transaction.** -/
def authBackend.ReadTx.spec : Prop :=
  ∀ (abe lg : Loc) (be tx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) ∗ retOk be go!"ReadTx" tx }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"ReadTx")) (Val #()))
  {{ (atx : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty) #atx);
      (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authReadTx.mk tx lg) : IProp GF) }}

end spec
end Schema
end EtcdGrove
end Perennial
