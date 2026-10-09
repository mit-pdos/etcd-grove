/-
`clientv3.OpGet(key, opts...)` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `OpGet(key, opts...)`: the `Op` modelled by `opGetModel key gs`; it panics if the options set both `WithPrefix` and `WithFromKey`, which the caller rules out. -/
abbrev OpGet.spec : Prop :=
  ∀ (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs ∗ ⌜¬ opGetPanics gs⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.OpGet)) (Val #key)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; opFullAt op (opGetModel key gs) }}

end spec

end EtcdGrove
end Perennial
