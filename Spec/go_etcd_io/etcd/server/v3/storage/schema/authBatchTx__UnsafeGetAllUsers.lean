/-
`(*authBatchTx).UnsafeGetAllUsers()` (`auth_users.go`): `unsafeGetAllUsers` on the transaction's
logger and `tx`, its users' bucket empty.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An `authBatchTx` whose `tx` is the reader `r` whose users' bucket is empty under `H`: `nil`. -/
abbrev schema.authBatchTx.UnsafeGetAllUsers.spec : Prop :=
  ∀ (atl lg : Loc) (r : GoInterfaceOk) (H : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atl ↦□ (GoInterface.ok r : GoInterface) ∗
      schema.abtF go!"lg" atl ↦□ lg ∗ H ∗
      schema.forEachUsersEmpty r H }}
    (App (Val (atl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetAllUsers")) (Val #()))
  {{ (s : GoSlice), RET #s; H ∗ s ↦* ([] : List Loc) }}

end spec

end EtcdGrove
end Perennial
