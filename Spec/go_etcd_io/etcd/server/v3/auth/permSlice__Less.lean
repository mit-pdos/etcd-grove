/-
`permSlice.Less` (`server/auth/store.go`): by key (`bytes.Compare`). Lean-first (no Rocq
counterpart; PR etcd#21845, `pr-verify/etcd-21845`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvRole

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3 auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `perms.Less(i, j)`: whether the `i`-th permission's key is less than the `j`-th's. -/
abbrev auth.permSlice.Less.spec : Prop :=
  ∀ (sl : GoSlice) (l : List (Loc × PermM)) (i j : w64) (a b : Loc × PermM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ownPerms sl l ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! permSlice.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (keyLt a.2 b.2)); ownPerms sl l }}

end spec

end EtcdGrove
end Perennial
