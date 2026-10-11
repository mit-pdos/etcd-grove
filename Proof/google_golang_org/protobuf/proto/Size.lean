/-
The trust boundary: `proto.Size` (names-only), of a `*pb.PutRequest`.
-/
module

public import Spec.google_golang_org.protobuf.proto.Size

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

axiom proto.Size.wp_proof : proto.Size.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
