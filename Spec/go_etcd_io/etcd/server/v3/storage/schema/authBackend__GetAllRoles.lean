/-
`(*authBackend).GetAllRoles()` (`auth_roles.go`): `BatchTx`, `Lock`, `UnsafeGetAllRoles`, the
deferred `Unlock`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBackend` over the backend `bi` with the logger `lg`: `bi.BatchTx()` returns a transaction
`t` whose `LockInsideApply()` goes from `R` to the token `Lk m` of a roles bucket `m` of role
encodings, whose range of it under the token is `authRolesRange`'s, and whose `Unlock()` and
`Commit()` go from `Lk m` to `C m` and on to `Q m`: returns the records of the range's entries
(`rolesOutD`), with `Q m`. -/
abbrev schema.authBackend.GetAllRoles.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (lg : Loc) (R : IProp GF) (Lk C Q : backend.BktData → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ schema.abeF go!"lg" abe ↦□ lg ∗ R ∗
      {{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
        {{ (tx : GoInterface), RET #tx; ∃ t : GoInterfaceOk, ⌜tx = GoInterface.ok t⌝ ∗
          ({{ R }} (App (Val #(methods t.ty go!"LockInsideApply" t.v)) (Val #()))
            {{ RET #(); ∃ m : backend.BktData, ⌜schema.rolesWf m⌝ ∗ Lk m }}) ∗
          (∀ m : backend.BktData, □ schema.authRolesRange t (Lk m) m) ∗
          (∀ m : backend.BktData, {{ Lk m }} (App (Val #(methods t.ty go!"Unlock" t.v)) (Val #())) {{ RET #(); C m }}) ∗
          (∀ m : backend.BktData, {{ C m }} (App (Val #(methods t.ty go!"Commit" t.v)) (Val #())) {{ RET #(); Q m }}) }} }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"GetAllRoles")) (Val #()))
  {{ (s : GoSlice), RET #s; ∃ m : backend.BktData, Q m ∗ schema.rolesOutD s (schema.rolesRangeEnts m) }}

end spec

end EtcdGrove
end Perennial
