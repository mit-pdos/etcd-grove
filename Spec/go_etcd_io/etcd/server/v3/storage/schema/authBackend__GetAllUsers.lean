/-
`(*authBackend).GetAllUsers()` (`auth_users.go`): `ReadTx`, `RLock`, `UnsafeGetAllUsers`, the
deferred `RUnlock`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBackend` over the backend `bi` (`authBE`) with the logger `lg`, the read resource `R`:
returns the users of some well-formed snapshot `D` of the auth buckets (`usersOutD`), which satisfies
every pure fact `Φ` the snapshot's token implies (the caller's: a token taken with the authority says
which state the buckets hold). -/
abbrev schema.authBackend.GetAllUsers.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (lg : Loc) (R : IProp GF) (Held : Loc → schema.AuthData → IProp GF)
    (Φ : schema.AuthData → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ schema.abeF go!"lg" abe ↦□ lg ∗
      schema.authBE bi R Held ∗ R ∗ □ (∀ (x : Loc) (D : schema.AuthData), Held x D -∗ Held x D ∗ ⌜Φ D⌝) }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"GetAllUsers")) (Val #()))
  {{ (s : GoSlice), RET #s; R ∗ ∃ D : schema.AuthData, ⌜schema.authWf D ∧ Φ D⌝ ∗
      schema.usersOutD s D.users }}

end spec

end EtcdGrove
end Perennial
