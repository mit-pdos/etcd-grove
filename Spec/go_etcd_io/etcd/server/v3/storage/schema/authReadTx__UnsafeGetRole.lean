/-
`(*authReadTx).UnsafeGetRole(roleName)` (`auth_roles.go`): `unsafeGetRole` on the transaction's
`lg` and `tx`. The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authReadTx` whose `tx` is the reader `rt` over the auth buckets `D` (its roles encodings)
under `H`: returns the role named `name` of `D.roles`, owned, or nil. -/
abbrev schema.authReadTx.UnsafeGetRole.spec : Prop :=
  ∀ (atx : Loc) (rt : GoInterfaceOk) (lg : Loc) (name : GoString) (H : IProp GF)
    (D : schema.AuthData), lg ≠ null → schema.rolesWf D.roles →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.atxF go!"tx" atx ↦□ (GoInterface.ok rt : GoInterface) ∗ schema.atxF go!"lg" atx ↦□ lg ∗
      schema.authReader rt H D ∗ H }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"UnsafeGetRole")) (Val #name))
  {{ (u : Loc), RET #u; H ∗ schema.roleOutDX u D.roles name }}

end spec

end EtcdGrove
end Perennial
