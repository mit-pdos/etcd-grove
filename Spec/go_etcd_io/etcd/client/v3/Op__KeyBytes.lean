/-
`clientv3.Op.KeyBytes()` (`client/v3/op.go`, translated for `client/v3/leasing`). Lean-first (no
Rocq counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.KeyBytes()` (called through a pointer): the key `key` (a read-only byte slice holding `o.key`). -/
abbrev Op.KeyBytes.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opFullAt op o }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"KeyBytes")) (Val #()))
  {{ (sl : GoSlice), RET #sl; opp ↦{dq} op ∗ sl ↦*□ o.key }}

end spec

end EtcdGrove
end Perennial
