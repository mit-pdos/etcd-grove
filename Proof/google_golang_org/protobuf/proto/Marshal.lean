/-
The trust boundary: `proto.Marshal` of an `mvccpb.KeyValue` (names-only; the encoding is
opaque, `Model.lean`).
-/
module

public import Spec.google_golang_org.protobuf.proto.Marshal

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

axiom proto.Marshal.wp_proof : proto.Marshal.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
