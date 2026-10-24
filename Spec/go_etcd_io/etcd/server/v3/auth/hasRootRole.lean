/-
`hasRootRole` (`server/auth/store.go`): `sort.SearchStrings` on the user's roles (proved since
the auth plan's S4b, 2026-10-24, over Perennial's `sort.wp_SearchStrings`; until then a
trust-boundary axiom). Lean-first (no Rocq counterpart; unit P2; the auth plan's S3 states its
result).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `hasRootRole(u)` of a user message holding the record `ur` (`ownUser`, S1) whose roles are
sorted (`UserGrantRole` sorts them; the backend's users are, `userOut`): `sort.SearchStrings(
u.Roles, "root")` and a bounds-checked index decide whether `"root"` is among them (`isRoot`),
the message kept. Trust boundary: `sort.SearchStrings` has no Perennial spec yet; with one,
`hasRootRole` is translated and this is proved (`notes/perennial-changes.md`). -/
abbrev auth.hasRootRole.spec : Prop :=
  ∀ (u : Loc) (ur : auth.UserRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.ownUser u ur ∗
      ⌜ur.roles.Pairwise go.GoStringLt⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.hasRootRole)) (Val #u))
  {{ (b : Bool), RET #b; auth.ownUser u ur ∗ ⌜b = decide (auth.isRoot ur.roles)⌝ }}

end spec

end EtcdGrove
end Perennial
