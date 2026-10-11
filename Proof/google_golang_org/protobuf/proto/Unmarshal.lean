/-
The trust boundary: `proto.Unmarshal` of an `mvccpb.KeyValue` (names-only; the encoding is
opaque, `Model.lean`).
-/
module

public import Spec.google_golang_org.protobuf.proto.Unmarshal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom proto.Unmarshal.wp_proof : proto.Unmarshal.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
