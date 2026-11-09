/-
## `(*authReadTx).UnsafeReadAuthRevision(...)`

**Users.** the auth store's revision reads (`auth/store.go`); 3d's auth store through `AuthBatchTx`/`AuthReadTx`. Snippet:
`examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).
**Proof sketch.** Loads `atx.tx`, `atx.lg`; `unsafeReadAuthRevision` (`unsafeReadAuthRevision.spec`). **Changes.** From
`specs-ref`'s `authReadTx__UnsafeReadAuthRevision.lean` where there was one: over the contract. **Margin.** None.
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

/-- **The auth revision** (`0` if absent). -/
def authReadTx.UnsafeReadAuthRevision.spec : Prop :=
  ∀ (atx : Loc) (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authReadTx.mk tx lg) : IProp GF) ∗ txRd tx S R ∗ R V ∗ ⌜S.has .auth authRevKey ∧ V .auth = some m ∧ authRevWf m⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"UnsafeReadAuthRevision")) (Val #()))
  {{ RET #(authRevOf m); R V }}

end spec
end Schema
end EtcdGrove
end Perennial
