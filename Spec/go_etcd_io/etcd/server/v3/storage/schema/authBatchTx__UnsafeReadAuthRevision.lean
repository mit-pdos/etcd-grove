/-
`(*authBatchTx).UnsafeReadAuthRevision` (`auth.go`/`auth_users.go`/`auth_roles.go`): `unsafeReadAuthRevision` on the transaction's `tx`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is the reader `t` over the auth buckets `D` (its revision 8
bytes) under `H`: returns `revisionOf D`. -/
abbrev schema.authBatchTx.UnsafeReadAuthRevision.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (H : IProp GF) (D : schema.AuthData), schema.revWf D.auth →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗
      schema.authReader t H D ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeReadAuthRevision")) (Val #()))
  {{ (x : w64), RET #x; H ∗ ⌜x = schema.revisionOf D⌝ }}

end spec

end EtcdGrove
end Perennial
