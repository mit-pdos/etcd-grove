/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_KV_Range_Handler.lean` (unit P3b). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._KV_Range_Handler
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

/-- The generated handler of `KV.Range`: decode a `*RangeRequest`, call `srv.Range` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.KV/Range"`), as every
generated unary handler (`wp_unaryHandler`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._KV_Range_Handler.wp_proof :
    etcdserverpb._KV_Range_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandler etcdserverpb._KV_Range_Handler etcdserverpb.KVServer.ty
    etcdserverpb.RangeRequest.ty etcdserverpb.RangeResponse.ty go!"Range" go!"/etcdserverpb.KV/Range"

end proof

end EtcdGrove
end Perennial
