/-
`(*authBackend).GetRole(roleName)` (`auth_roles.go`): `UnsafeGetRole` under a read-locked read
transaction (`RLock`, deferred `RUnlock`). The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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
returns the role named `name` of some well-formed snapshot of the auth buckets, owned, or nil. -/
abbrev schema.authBackend.GetRole.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (lg : Loc) (R : IProp GF) (Held : Loc → schema.AuthData → IProp GF)
    {ι : Type} (L : ι → IProp GF) (i : ι)
    (Φ : schema.AuthData → Prop) (dR : schema.AuthData → GoString → auth.RoleRec) (name : GoString),
  (∀ D : schema.AuthData, schema.authWf D → Φ D → schema.rolesDec D.roles (dR D)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ schema.abeF go!"lg" abe ↦□ lg ∗
      schema.authBE bi R L Held ∗ R ∗ L i ∗
      □ (∀ (x : Loc) (D : schema.AuthData), Held x D -∗ Held x D ∗ ⌜Φ D⌝) }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"GetRole")) (Val #name))
  {{ (u : Loc), RET #u; R ∗ L i ∗ ∃ D : schema.AuthData, ⌜schema.authWf D ∧ Φ D⌝ ∗
      schema.roleOutD u D.roles name (dR D) }}

end spec

end EtcdGrove
end Perennial
