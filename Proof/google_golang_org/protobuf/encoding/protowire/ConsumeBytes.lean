/-
The trust boundary: `protowire.ConsumeBytes`
(`google.golang.org/protobuf/encoding/protowire` is names-only).
-/
module

public import Spec.google_golang_org.protobuf.encoding.protowire.ConsumeBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf.encoding

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom protowire.ConsumeBytes.wp_proof : protowire.ConsumeBytes.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
