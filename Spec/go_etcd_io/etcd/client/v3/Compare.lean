/-
`clientv3.Compare(cmp, result, v)` (`client/v3/compare.go`, translated for `client/v3/concurrency`). Lean-first (no
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

/-- `Compare(cmp, result, v)`: a fresh clone of `cmp` with the operator `result` (`"="`, `"!="`,
`">"`, `"<"`) and the operand `v` (a `string` for a value comparison, an integer otherwise:
`cmpArgOf`); anything else panics, which the caller rules out. -/
abbrev Compare.spec : Prop :=
  ∀ (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) (result : GoString) (op : CmpOp) (v : GoInterface)
    (x : CmpArg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpAt c m ∗ ⌜cmpOpOf result = some op ∧ cmpArgOf m.target v x⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.Compare)) (Val #c)) (Val #result)) (Val #v))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpAt c' (compareM m op x) }}

end spec

end EtcdGrove
end Perennial
