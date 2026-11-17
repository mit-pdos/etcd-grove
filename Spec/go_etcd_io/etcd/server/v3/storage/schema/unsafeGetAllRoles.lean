/-
`unsafeGetAllRoles(lg, tx)` (`auth_roles.go`): `UnsafeRange(AuthRoles, []byte{0}, []byte{0xff}, -1)`,
then decodes each value (`proto.Unmarshal`) into a fresh message of a fresh slice. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- The reader `r` whose range of the roles bucket `m` under `H` is `authRolesRange`'s (a batch
transaction), its values role encodings: returns the records of the range's entries
(`rolesRangeEnts m`), one fresh message each, in order (`rolesOutD`; nil if there is none). The panic
(a value that does not decode) is not reached (`rolesWf`). -/
abbrev schema.unsafeGetAllRoles.spec : Prop :=
  ∀ (lg : Loc) (r : GoInterfaceOk) (H : IProp GF) (m : backend.BktData), schema.rolesWf m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ □ schema.authRolesRange r H m ∗ H }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllRoles)) (Val #lg)) (Val #(GoInterface.ok r)))
  {{ (s : GoSlice), RET #s; H ∗ schema.rolesOutD s (schema.rolesRangeEnts m) }}

end spec

end EtcdGrove
end Perennial
