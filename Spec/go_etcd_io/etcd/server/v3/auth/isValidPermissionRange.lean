/-
`isValidPermissionRange` (`server/auth/range_perm_cache.go`): the trust boundary (names
only). Lean-first (no Rocq counterpart; PR etcd#21845, `pr-verify/etcd-21845`).
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

/-- `isValidPermissionRange(key, rangeEnd)` returns, keeping the slices (no claim on the
result). -/
abbrev auth.isValidPermissionRange.spec : Prop :=
  ∀ (key re : GoSlice) (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ key ↦*{dk} k ∗
      re ↦*{de} e }}
    (App (App (Val (@! isValidPermissionRange)) (Val #key)) (Val #re))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e }}

end spec

end EtcdGrove
end Perennial
