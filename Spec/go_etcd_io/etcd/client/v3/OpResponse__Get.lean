/-
`clientv3.OpResponse.Get()` (`client/v3/op.go`, translated for `client/v3/leasing`). Lean-first (no Rocq counterpart).
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

/-- `r.Get()`: the `OpResponse`'s `get` field. -/
abbrev OpResponse.Get.spec : Prop :=
  ∀ (r : go_etcd_io.etcd.client.v3.OpResponse),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (r @!! go_etcd_io.etcd.client.v3.OpResponse.ty @!! go!"Get")) (Val #()))
  {{ RET #r.get'; True }}

end spec

end EtcdGrove
end Perennial
