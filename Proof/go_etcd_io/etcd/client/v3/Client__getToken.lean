/-
**Trust boundary**: the client's `getToken` (its auth part) returns `nil` or a client error (an axiom; see `Spec/go_etcd_io/etcd/client/v3/Client__getToken.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__getToken

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary**: the client's `getToken` (its auth part) returns `nil` or a client error. -/
axiom Client.getToken.wp_proof : Client.getToken.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
