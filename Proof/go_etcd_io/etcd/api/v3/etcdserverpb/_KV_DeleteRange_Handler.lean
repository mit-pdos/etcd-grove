/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_KV_DeleteRange_Handler.lean` (unit P3b). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._KV_DeleteRange_Handler
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.UnaryHandlerLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The generated handler of `KV.DeleteRange`: decode a `*DeleteRangeRequest`, call `srv.DeleteRange` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.KV/DeleteRange"`), as every
generated unary handler (`wp_unaryHandler`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._KV_DeleteRange_Handler.wp_proof :
    etcdserverpb._KV_DeleteRange_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandler etcdserverpb._KV_DeleteRange_Handler etcdserverpb.KVServer.ty
    etcdserverpb.DeleteRangeRequest.ty etcdserverpb.DeleteRangeResponse.ty go!"DeleteRange" go!"/etcdserverpb.KV/DeleteRange"

end proof

end EtcdGrove
end Perennial
