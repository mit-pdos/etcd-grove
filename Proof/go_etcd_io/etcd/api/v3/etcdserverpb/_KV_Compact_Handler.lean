/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_KV_Compact_Handler.lean` (unit P3b). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._KV_Compact_Handler
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.UnaryHandlerLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The generated handler of `KV.Compact`: decode a `*CompactionRequest`, call `srv.Compact` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.KV/Compact"`), as every
generated unary handler (`wp_unaryHandlerMd`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._KV_Compact_Handler.wp_proof :
    etcdserverpb._KV_Compact_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandlerOwnMd etcdserverpb._KV_Compact_Handler etcdserverpb.KVServer.ty
    etcdserverpb.CompactionRequest.ty etcdserverpb.CompactionResponse.ty go!"Compact" go!"/etcdserverpb.KV/Compact"

end proof

end EtcdGrove
end Perennial
