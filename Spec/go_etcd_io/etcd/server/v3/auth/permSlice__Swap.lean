/-
`permSlice.Swap` (`server/auth/store.go`): exchanges two pointers. Lean-first (no Rocq
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

/-- `perms.Swap(i, j)`: the `i`-th and `j`-th pointers exchanged. -/
abbrev auth.permSlice.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (i j : w64) (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ sl ↦* ps ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ps[sint.nat i]? = some a ∧ ps[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! permSlice.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* (ps.set (sint.nat i) b).set (sint.nat j) a }}

end spec

end EtcdGrove
end Perennial
