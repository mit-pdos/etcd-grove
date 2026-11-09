/-
## `(*authBackend).GetUser(name)`

**Users.** `authStore.UserGet`-like reads and checks outside a write (`auth/store.go:341,590`). Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `ReadTx()` (`authBackend.ReadTx.spec`), `RLock()` (`rdSect`: the view, the bucket
present and its records decoding), the `authReadTx` read, the deferred `RUnlock()` (`rdSect`).

**Changes.** From `specs-ref`'s `authBackend__GetUser.lean` where there was one (the old backend's read
pool): over the read section's triples. **Margin.** None.
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

/-- **The record `name`** (or `nil`) of the view a read section sees. -/
def authBackend.GetUser.spec : Prop :=
  ∀ (abe lg : Loc) (be rtx : GoInterface) (S : Scope) (R : View → IProp GF) (P : IProp GF)
    (Q : View → IProp GF) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) ∗ retOk be go!"ReadTx" rtx ∗ txRd rtx S R ∗ ⌜S.has .authUsers name⌝ ∗
      rdSect rtx P R (fun V => ∃ m, V .authUsers = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.User.ty m) Q ∗ P }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"GetUser")) (Val #name))
  {{ (p : Loc), RET #p; ∃ V m, Q V ∗ ⌜V .authUsers = some m⌝ ∗ recRes go_etcd_io.etcd.api.v3.authpb.User.ty (m name) p }}

end spec
end Schema
end EtcdGrove
end Perennial
