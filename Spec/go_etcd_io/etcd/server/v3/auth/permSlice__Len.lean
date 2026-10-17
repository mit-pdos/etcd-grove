/-
`permSlice.Len` (`server/auth/store.go`): the length of the slice. Lean-first (no Rocq
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

/-- `perms.Len()`: the number of permissions. -/
abbrev auth.permSlice.Len.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ sl ↦*{dq} ps }}
    (App (Val (sl @!! permSlice.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ps.length); sl ↦*{dq} ps }}

end spec

end EtcdGrove
end Perennial
