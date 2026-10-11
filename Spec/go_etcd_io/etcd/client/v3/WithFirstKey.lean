/-
`clientv3.WithFirstKey()` (`client/v3/op.go`, translated for `client/v3/experimental/recipes`); see
`InvOp.lean`. Lean-first (no Rocq counterpart).
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

/-- `WithFirstKey()`: `withTop(SortByKey, SortAscend)`, the lexically first key in the range, a
fresh slice of options. Its sort option is `WithSort(SortByKey, SortAscend)`, whose closure
rewrites the `order` it captured to `SortNone` (which `WithSort.spec`, a persistent closure spec,
excludes: two concurrent calls would race on it); so the slice's closures need that variable, a
resource `R` passed from call to call (`optsAtRes`; the client's `Get` at `context.TODO()` takes
such options, `isEtcdKVTodo`). -/
abbrev WithFirstKey.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithFirstKey)) (Val #()))
  {{ (sl : GoSlice), RET #sl; (∃ R : IProp GF, R ∗ optsAtRes sl (withTopM (W64 0) (W64 1)) R) ∗
      ownSliceCap GoFunc sl (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
