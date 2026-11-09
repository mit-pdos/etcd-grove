/-
## `(*authBatchTx).UnsafePutRole(msg)`

**Users.** `RoleAdd`, `RoleGrantPermission`, `RoleRevokePermission` (`auth/store.go`). Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `proto.Marshal(msg)` (`Proto.Marshal.spec`: `fits`, `marshalOk`: no error, so
`lg.Panic` unreachable), the fresh bytes made read-only; the message's `Name` field (3h's law: its
slice holds `roleName c`, read-only for good at `discard`); `tx.UnsafePut(AuthRoles, Name, bytes)` (`txWr`:
the backend keeps both slices, hence the message read-only for good; bbolt's limits: `putFits`, the
auth store's `Auth.recordsFit`, round 1, F4).

**Changes.** New (the old auth proofs had no batch-side spec). **Margin.** The value is any encoding
of the content (`Marshal` is deterministic for these map-free types: `Proto.marshalOut`).
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

/-- **Stores the record** under its name. -/
def authBatchTx.UnsafePutRole.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m0 : BData)
    (p : Loc) (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txWr tx S R ∗ R V ∗ ⌜S.has .authRoles (roleName c) ∧ V .authRoles = some m0⌝ ∗
      Proto.msgAt go_etcd_io.etcd.api.v3.authpb.Role.ty p DFrac.discard c ∗ ⌜c.fits ∧ Proto.marshalOk c⌝ ∗
      ⌜∀ bs, Proto.encodes go_etcd_io.etcd.api.v3.authpb.Role.ty c bs → putFits (roleName c) bs⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafePutRole")) (Val #p))
  {{ RET #(); ∃ bs : GoString, ⌜Proto.encodes go_etcd_io.etcd.api.v3.authpb.Role.ty c bs⌝ ∗ R (V.put .authRoles (roleName c) bs) }}

end spec
end Schema
end EtcdGrove
end Perennial
