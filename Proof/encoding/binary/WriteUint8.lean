/-
The trust boundary: `encoding/binary`'s `Write` of an integer (names-only in Perennial).
-/
module

public import Spec.encoding.binary.WriteUint8

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom binary.WriteUint8.wp_proof : binary.WriteUint8.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
