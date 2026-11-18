/-
`(*authBatchTx).UnsafeGetUser` (`auth.go`/`auth_users.go`/`auth_roles.go`): `unsafeGetUser` on the transaction's `lg` and `tx`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is the reader `t` over the auth buckets `D` (its users the encodings of the records `dU` names)
under `H`: returns the user named `name` of `D.users`, owned (the record `dU name`), or nil. -/
abbrev schema.authBatchTx.UnsafeGetUser.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (lg : Loc) (name : GoString) (H : IProp GF) (D : schema.AuthData) (dU : GoString → auth.UserRec), lg ≠ null → schema.usersDec D.users dU →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ schema.abtF go!"lg" atx ↦□ lg ∗
      schema.authReader t H D ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetUser")) (Val #name))
  {{ (u : Loc), RET #u; H ∗ schema.userOutDX u D.users name dU }}

end spec

end EtcdGrove
end Perennial
