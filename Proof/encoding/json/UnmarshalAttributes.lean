/-
The trust boundary: `json.Unmarshal` on `*membership.Attributes` (`encoding/json` is names-only).
-/
module

public import Spec.encoding.json.UnmarshalAttributes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom json.UnmarshalAttributes.wp_proof : json.UnmarshalAttributes.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
