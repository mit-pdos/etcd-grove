/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__streamClientInterceptor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary** (item 5): `streamClientInterceptor(optFuncs...)` builds its options
(`reuseOrNewWithCallOptions(defaultOptions, optFuncs)`: each option's closure, which returns,
`optApplyOk`) and returns its closure, etcd's stream interceptor: the one grpc's
`ClientConn.NewStream` axiom assumes (`withVersion`'s metadata, `getToken`, the call options
filtered, no retry at `withMax(0)`). -/
axiom Client.streamClientInterceptor.wp_proof : Client.streamClientInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
