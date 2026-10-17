/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__Close.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__Close

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

/-- **Trust boundary** (item 5): `Close()` is the embedded `manual.Resolver`'s (grpc v1.84.0),
which calls its `CloseCallback` (a no-op unless set; etcd does not set it). -/
axiom resolver.EtcdManualResolver.Close.wp_proof :
  resolver.EtcdManualResolver.Close.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
