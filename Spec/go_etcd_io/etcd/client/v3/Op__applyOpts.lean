/-
`clientv3.Op.applyOpts(opts)` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `op.applyOpts(opts)`: the options applied in order (`opFold`). -/
abbrev Op.applyOpts.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (sl : GoSlice) (gs : List (OpFull → OpFull)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦ op ∗ opFullAt op o ∗ optsAt sl gs }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"applyOpts")) (Val #sl))
  {{ (op' : go_etcd_io.etcd.client.v3.Op), RET #(); opp ↦ op' ∗ opFullAt op' (opFold gs o) }}

end spec

end EtcdGrove
end Perennial
