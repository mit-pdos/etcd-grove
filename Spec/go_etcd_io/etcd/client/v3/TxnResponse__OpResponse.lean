/-
`clientv3.TxnResponse.OpResponse()` (`client/v3/kv.go`, translated for `client/v3/leasing`). Lean-first (no Rocq counterpart).
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

/-- `resp.OpResponse()`: `OpResponse{txn: resp}`. -/
abbrev TxnResponse.OpResponse.spec : Prop :=
  ∀ (resp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (resp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.TxnResponse.ty @!! go!"OpResponse")) (Val #()))
  {{ RET #(go_etcd_io.etcd.client.v3.OpResponse.mk null null null resp); True }}

end spec

end EtcdGrove
end Perennial
