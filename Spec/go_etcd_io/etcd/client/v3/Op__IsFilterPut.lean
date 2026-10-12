/-
`clientv3.Op.IsFilterPut()` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
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

/-- `op.IsFilterPut()`: whether `WithFilterPut` is set, `o.filterPut`. -/
abbrev Op.IsFilterPut.spec : Prop :=
  ∀ (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opAt op o }}
    (App (Val (op @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"IsFilterPut")) (Val #()))
  {{ RET #(o.filterPut); True }}

end spec

end EtcdGrove
end Perennial
