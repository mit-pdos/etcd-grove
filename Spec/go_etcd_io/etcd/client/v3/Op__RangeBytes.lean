/-
`clientv3.Op.RangeBytes()` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.RangeBytes()` (called through a pointer, as the cache does): the range end `end` (a read-only byte slice), `o.rangeEnd`. A read, on
any fraction. -/
abbrev Op.RangeBytes.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"RangeBytes")) (Val #()))
  {{ (sl : GoSlice), RET #sl; opp ↦{dq} op ∗ sl ↦*□ o.rangeEnd }}

end spec

end EtcdGrove
end Perennial
