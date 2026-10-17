/-
**Trust boundary**: `json.Unmarshal` decodes a `HashKVRequest` (an axiom; see `Spec/encoding/json/UnmarshalHashKVRequest.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.encoding.json.UnmarshalHashKVRequest

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

/-- **Trust boundary**: `json.Unmarshal` decodes a `HashKVRequest`. -/
axiom json.UnmarshalHashKVRequest.wp_proof : json.UnmarshalHashKVRequest.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
