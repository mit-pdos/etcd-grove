/-
The trust boundary: `encoding/binary`'s `Write` of an integer (names-only in Perennial).
-/
module

public import Spec.encoding.binary.WriteUint64

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

axiom binary.WriteUint64.wp_proof : binary.WriteUint64.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
