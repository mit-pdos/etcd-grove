/-
`(*authBatchTx).UnsafeGetRole` (`auth.go`/`auth_users.go`/`auth_roles.go`): `unsafeGetRole` on the transaction's `lg` and `tx`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is the reader `t` over the auth buckets `D` (its roles the encodings of the records `dR` names)
under `H`: returns the role named `name` of `D.roles`, owned (the record `dR name`), or nil. -/
abbrev schema.authBatchTx.UnsafeGetRole.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (lg : Loc) (name : GoString) (H : IProp GF) (D : schema.AuthData) (dR : GoString → auth.RoleRec), lg ≠ null → schema.rolesDec D.roles dR →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ schema.abtF go!"lg" atx ↦□ lg ∗
      schema.authReader t H D ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetRole")) (Val #name))
  {{ (r : Loc), RET #r; H ∗ schema.roleOutDX r D.roles name dR }}

end spec

end EtcdGrove
end Perennial
