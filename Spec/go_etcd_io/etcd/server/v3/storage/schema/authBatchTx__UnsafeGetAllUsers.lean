/-
`(*authBatchTx).UnsafeGetAllUsers` (`auth.go`/`auth_users.go`/`auth_roles.go`): `unsafeGetAllUsers` on the transaction's `lg` and `tx`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An `authBatchTx` whose `tx` is the reader `t` over the auth buckets `D` (its users encodings)
under `H`: returns the users bucket's records (`usersOutD`). -/
abbrev schema.authBatchTx.UnsafeGetAllUsers.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (lg : Loc) (H : IProp GF) (D : schema.AuthData), schema.usersWf D.users →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ schema.abtF go!"lg" atx ↦□ lg ∗
      schema.authReader t H D ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetAllUsers")) (Val #()))
  {{ (s : GoSlice), RET #s; H ∗ schema.usersOutD s D.users }}

end spec

end EtcdGrove
end Perennial
