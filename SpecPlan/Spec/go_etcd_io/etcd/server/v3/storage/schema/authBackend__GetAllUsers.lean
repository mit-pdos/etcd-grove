/-
## `(*authBackend).GetAllUsers()`

**Users.** `UserList` (`auth/store.go:602`). Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `ReadTx()` (`authBackend.ReadTx.spec`), `RLock()` (`rdSect`: the view, the bucket
present and its records decoding), the `authReadTx` read, the deferred `RUnlock()` (`rdSect`).

**Changes.** From `specs-ref`'s `authBackend__GetAllUsers.lean` where there was one (the old backend's read
pool): over the read section's triples. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- **Every record**, each once, in some order, of the view a read section sees. -/
def authBackend.GetAllUsers.spec : Prop :=
  ∀ (abe lg : Loc) (be rtx : GoInterface) (S : Scope) (R : View → IProp GF) (P : IProp GF)
    (Q : View → IProp GF) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) ∗ retOk be go!"ReadTx" rtx ∗ txRd rtx S R ∗ ⌜S.whole .authUsers⌝ ∗
      rdSect rtx P R (fun V => ∃ m, V .authUsers = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.User.ty m) Q ∗ P }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"GetAllUsers")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ V m l, Q V ∗ ⌜V .authUsers = some m ∧ entsAny m l⌝ ∗ recsRes go_etcd_io.etcd.api.v3.authpb.User.ty sl (l.map Prod.snd) }}

end spec
end Schema
end EtcdGrove
end Perennial
