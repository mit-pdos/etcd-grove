/-
`clientv3.Cmp.WithRange(end)` (`client/v3/compare.go`, translated for `client/v3/concurrency`). Lean-first (no
Rocq counterpart); see `InvCmp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCmp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cmp.WithRange(end)`: a fresh clone of `cmp` comparing the keys of `[key, end)`. -/
abbrev Cmp.WithRange.spec : Prop :=
  ∀ (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) (endKey : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpAt c m }}
    (App (Val (c @!! go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"WithRange")) (Val #endKey))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpAt c' (cmpWithRangeM endKey m) }}

end spec

end EtcdGrove
end Perennial
