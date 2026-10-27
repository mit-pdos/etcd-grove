/-
`schema.unsafeGetRole(lg, tx, roleName)` (`auth_roles.go`): the role's message, decoded from the
`authRoles` bucket's value at its name (`proto.Unmarshal`, the trust boundary; every value an
encoding, `rolesWf`, else the function panics), nil if none (`roleOutD`), read through the
`UnsafeReader` `tx` over the snapshot `D` under the token `H`. The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- The reader `r` over the auth buckets `D` (its roles encodings) under `H`: returns the role
named `name` of `D.roles`, owned, or nil. -/
abbrev schema.unsafeGetRole.spec : Prop :=
  ∀ (lg : Loc) (r : GoInterfaceOk) (name : GoString) (H : IProp GF) (D : schema.AuthData),
  lg ≠ null → schema.rolesWf D.roles →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.authReader r H D ∗ H }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetRole)) (Val #lg)) (Val #(GoInterface.ok r)))
      (Val #name))
  {{ (u : Loc), RET #u; H ∗ schema.roleOutDX u D.roles name }}

end spec

end EtcdGrove
end Perennial
