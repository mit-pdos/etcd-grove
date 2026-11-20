/-
`(*authBatchTx).UnsafeGetAllRoles()` (`auth_roles.go`): `unsafeGetAllRoles` on the transaction's `lg`
and `tx`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` ranges the roles bucket `m` under `H` (`authRolesRange`), its values
the encodings of the records `dR` names: returns the records of the range's entries (`rolesOutD`). -/
abbrev schema.authBatchTx.UnsafeGetAllRoles.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (lg : Loc) (H : IProp GF) (m : backend.BktData) (dR : GoString → auth.RoleRec),
  schema.rolesDec m dR →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ schema.abtF go!"lg" atx ↦□ lg ∗
      □ schema.authRolesRange t H m ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetAllRoles")) (Val #()))
  {{ (s : GoSlice), RET #s; H ∗ schema.rolesOutD s (schema.rolesRangeEnts m) dR }}

end spec

end EtcdGrove
end Perennial
