/-
`unsafeGetAllUsers(lg, tx)` (`auth_users.go`): walks the users bucket (`UnsafeForEach`, the visitor
appending each value to `vs`), then decodes each value (`proto.Unmarshal`) into a fresh message of a
fresh slice. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- The reader `r` over the auth buckets `D` (its users encodings) under `H`: returns the users bucket's
records, one fresh message per entry (`usersOutD`; nil if there is none). The two panics (the walk's
error, a value that does not decode) are not reached: the walk returns nil (`authForEachSpec`) and
every value is an encoding (`usersWf`). -/
abbrev schema.unsafeGetAllUsers.spec : Prop :=
  ∀ (lg : Loc) (r : GoInterfaceOk) (H : IProp GF) (D : schema.AuthData), schema.usersWf D.users →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.authReader r H D ∗ H }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllUsers)) (Val #lg)) (Val #(GoInterface.ok r)))
  {{ (s : GoSlice), RET #s; H ∗ schema.usersOutD s D.users }}

end spec

end EtcdGrove
end Perennial
