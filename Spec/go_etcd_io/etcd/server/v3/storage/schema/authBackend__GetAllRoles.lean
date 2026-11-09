/-
## `(*authBackend).GetAllRoles()`

**Users.** `RoleList`, `refreshRangePermCache` (`auth/store.go:677`; called by the auth store's writer
only, 3d). Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `BatchTx()`, `Lock()` (`LockInsideApply`: `wrSect`), `UnsafeGetAllRoles()`
(`txRange`), the deferred `Unlock()` (`Unlock` then `Commit`: `wrSect` and the commit's triple).

**Changes.** New (on the batch transaction: the read transaction's interval range panics,
`nonissues/etcd-auth-readtx-getallroles-panics.md`). **Margin.** None.
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

/-- **Every role** (names in `[0x00, 0xff)`), in name order, of the batch view in a write section. -/
def authBackend.GetAllRoles.spec : Prop :=
  ∀ (abe lg : Loc) (be btx : GoInterface) (S : Scope) (R : View → IProp GF) (P : IProp GF)
    (Q1 Q : View → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) ∗ retOk be go!"BatchTx" btx ∗ txRange btx S R ∗ ⌜S.whole .authRoles⌝ ∗
      wrSect btx go!"LockInsideApply" P R (fun V => ∃ m, V .authRoles = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.Role.ty m) Q1 ∗
      (∀ V, callOk btx go!"Commit" (Q1 V) (Q V)) ∗ P }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"GetAllRoles")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ V m l, Q V ∗ ⌜V .authRoles = some m ∧ rangeOf m [W8 0] [W8 255] (-1) l⌝ ∗
      recsRes go_etcd_io.etcd.api.v3.authpb.Role.ty sl (l.map Prod.snd) }}

end spec
end Schema
end EtcdGrove
end Perennial
