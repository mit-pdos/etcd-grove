/-
`clientv3.WithLastCreate()` (`client/v3/op.go`, translated for `client/v3/concurrency`). Lean-first (no Rocq
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

/-- `WithLastCreate()`: `withTop(SortByCreateRevision, SortDescend)`, the key with the latest
create revision in the range. -/
abbrev WithLastCreate.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithLastCreate)) (Val #()))
  {{ (sl : GoSlice), RET #sl; optsAt sl (withTopM (W64 2) (W64 2)) }}

end spec

end EtcdGrove
end Perennial
