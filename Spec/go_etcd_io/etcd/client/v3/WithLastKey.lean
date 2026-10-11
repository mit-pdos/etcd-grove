/-
`clientv3.WithLastKey()` (`client/v3/op.go`, translated for `client/v3/experimental/recipes`); see
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

/-- `WithLastKey()`: the lexically last key in the range (`withTop(SortByKey, SortDescend)`), a fresh slice of options. -/
abbrev WithLastKey.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithLastKey)) (Val #()))
  {{ (sl : GoSlice), RET #sl; optsAt sl (withTopM (W64 0) (W64 2)) ∗
      ownSliceCap GoFunc sl (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
