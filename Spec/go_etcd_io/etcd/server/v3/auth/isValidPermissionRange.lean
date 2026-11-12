/-
`isValidPermissionRange` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2; the auth plan's S2, 2026-10-23).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `isValidPermissionRange(key, rangeEnd)`: the model's `rangeValid` (a non-empty key; a point,
a range with `key < rangeEnd` in the bytes-affine order, or an open-ended range); the slices
kept. -/
abbrev auth.isValidPermissionRange.spec : Prop :=
  ∀ (key re : GoSlice) (k e : GoString) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ key ↦*{dk} k ∗
      re ↦*{de} e }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.isValidPermissionRange)) (Val #key))
      (Val #re))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜b = true ↔ rangeValid k e⌝ }}

end spec

end EtcdGrove
end Perennial
