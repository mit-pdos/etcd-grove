/-
`clientv3.Op.ValueBytes()` (`client/v3/op.go`, translated for `client/v3/leasing`). Lean-first (no
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

/-- `op.ValueBytes()`: the value `val` (a read-only byte slice holding `o.val`). -/
abbrev Op.ValueBytes.spec : Prop :=
  ∀ (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opFullAt op o }}
    (App (Val (op @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"ValueBytes")) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦*□ o.val }}

end spec

end EtcdGrove
end Perennial
