/-
## `(*authBackend).CreateAuthBuckets()`

**Users.** `NewAuthStore` (`auth/store.go:972`). Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `be.BatchTx()` (`retOk`), `LockOutsideApply()` (`wrSect`), three
`UnsafeCreateBucket`s (`txWr`), the deferred `Unlock()` (`wrSect`).

**Changes.** New. **Margin.** None.
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

/-- **Creates the three auth buckets** in a write section. -/
def authBackend.CreateAuthBuckets.spec : Prop :=
  ∀ (abe lg : Loc) (be btx : GoInterface) (S : Scope) (R : View → IProp GF) (P : IProp GF)
    (Q : View → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) ∗ retOk be go!"BatchTx" btx ∗ txWr btx S R ∗
      ⌜S.whole .auth ∧ S.whole .authUsers ∧ S.whole .authRoles⌝ ∗
      wrSect btx go!"LockOutsideApply" P R (fun _ => True) Q ∗ P }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"CreateAuthBuckets")) (Val #()))
  {{ RET #(); ∃ V : View, Q (((V.create .auth).create .authUsers).create .authRoles) }}

end spec
end Schema
end EtcdGrove
end Perennial
