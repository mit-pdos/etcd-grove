/-
The trust boundary of `encoding.json.MarshalMember` (see its spec).
-/
module

public import Spec.encoding.json.MarshalMember

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom encoding.json.MarshalMember.wp_proof : encoding.json.MarshalMember.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
