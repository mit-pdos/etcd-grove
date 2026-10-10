/-
`etcdserverpb.ResponseOp.GetResponsePut()` (`api/etcdserverpb/rpc.pb.go`, translated for `client/v3/leasing`); see `InvEtcdTxnOwn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `p.GetResponsePut()` of a non-nil `*ResponseOp` whose `Response` oneof holds a `*ResponseOp_ResponsePut` `w`:
`w.ResponsePut` (read-only). -/
abbrev ResponseOp.GetResponsePut.spec : Prop :=
  ∀ (p w x : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ x }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.ResponseOp.ty @!! go!"GetResponsePut"))
      (Val #()))
  {{ RET #x; True }}

end spec

end EtcdGrove
end Perennial
