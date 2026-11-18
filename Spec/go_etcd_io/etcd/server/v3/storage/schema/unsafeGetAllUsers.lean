/-
`unsafeGetAllUsers(lg, tx)` (`auth_users.go`), on a reader whose users' bucket is empty: `nil`.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The reader `r` under the token `H`, its `UnsafeForEach` over the `AuthUsers` bucket returning
`nil` without calling the visitor (an empty users' bucket): `nil` (`len(vs) == 0`); no decoding, no
panic. Only the empty case (the general one decodes every user record: `proto.Unmarshal`). -/
abbrev schema.unsafeGetAllUsers.spec : Prop :=
  ∀ (lg : Loc) (r : GoInterfaceOk) (H : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ H ∗
      schema.forEachUsersEmpty r H }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllUsers)) (Val #lg)) (Val #(GoInterface.ok r)))
  {{ (s : GoSlice), RET #s; H ∗ s ↦* ([] : List Loc) }}

end spec

end EtcdGrove
end Perennial
