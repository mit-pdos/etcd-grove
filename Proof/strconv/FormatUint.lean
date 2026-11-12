/-
The trust boundary: `strconv.FormatUint` (Perennial's `strconv` is names-only; `FormatUint` of a base in `2..36` returns its digits).
-/
module

public import Spec.strconv.FormatUint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom strconv.FormatUint.wp_proof : strconv.FormatUint.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
