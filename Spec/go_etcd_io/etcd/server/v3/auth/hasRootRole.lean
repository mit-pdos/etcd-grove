/-
`hasRootRole` (`server/auth/store.go`): the trust boundary (names only: it reads `u.Roles` of
the protobuf `authpb.User`, an axiomatized type). Lean-first (no Rocq counterpart; unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

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

/-- `hasRootRole(u)` of a non-nil user (`sort.SearchStrings(u.Roles, "root")` and a
bounds-checked index): some boolean. The user's points-to is not stated: `authpb.User` is an
axiomatized type whose typed points-to is a generated `sorry` instance. -/
abbrev auth.hasRootRole.spec : Prop :=
  ∀ (u : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜u ≠ null⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.hasRootRole)) (Val #u))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
