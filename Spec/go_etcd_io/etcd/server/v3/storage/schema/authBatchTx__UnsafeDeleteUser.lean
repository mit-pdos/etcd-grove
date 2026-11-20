/-
`(*authBatchTx).UnsafeDeleteUser(name)` (`auth_users.go`/`auth_roles.go`): `tx.UnsafeDelete(AuthUsers, []byte(name))`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is `t`: one call of `t`, `UnsafeDelete` from the bucket `bk` the
variable `schema.AuthUsers` holds of the key `name` (a fresh slice, the caller's): given that
delete's triple from `R` to `Q`, it goes from `R` to `Q`. -/
abbrev schema.authBatchTx.UnsafeDeleteUser.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (name : GoString) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ R ∗
      □ (∀ (bk : GoInterface) (key : GoSlice),
        {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ bk ∗ key ↦* name ∗ R }}
          (App (App (Val #(methods t.ty go!"UnsafeDelete" t.v)) (Val #bk)) (Val #key))
        {{ RET #(); Q }}) }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeDeleteUser")) (Val #name))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
