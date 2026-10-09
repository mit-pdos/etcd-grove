/-
`clientv3.OpPut(key, val, opts...)` (`client/v3/op.go`, translated for `client/v3/concurrency`). Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

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

/-- `OpPut(key, val, opts...)`: the `Op` modelled by `opPutModel key val gs`; it panics if the
options set something a put cannot have, which the caller rules out (`putPanics`). -/
abbrev OpPut.spec : Prop :=
  ∀ (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs ∗ ⌜¬ (opPutModel key val gs).putPanics⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.OpPut)) (Val #key)) (Val #val)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; opFullAt op (opPutModel key val gs) }}

end spec

end EtcdGrove
end Perennial
