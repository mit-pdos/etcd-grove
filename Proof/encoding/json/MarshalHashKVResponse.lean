/-
**Trust boundary**: `json.Marshal` encodes a `HashKVResponse` (an axiom; see `Spec/encoding/json/MarshalHashKVResponse.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.encoding.json.MarshalHashKVResponse

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Trust boundary**: `json.Marshal` encodes a `HashKVResponse`. -/
axiom json.MarshalHashKVResponse.wp_proof : json.MarshalHashKVResponse.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
