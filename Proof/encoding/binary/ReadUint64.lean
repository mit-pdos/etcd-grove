/-
The trust boundary: `encoding/binary`'s `Read` of an integer (names-only in Perennial).
-/
module

public import Spec.encoding.binary.ReadUint64

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

axiom binary.ReadUint64.wp_proof : binary.ReadUint64.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
