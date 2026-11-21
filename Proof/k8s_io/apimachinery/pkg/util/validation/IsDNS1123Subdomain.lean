/-
`validation.IsDNS1123Subdomain(value)` (apimachinery, names only): **the trust boundary**. The
axiom (see its docstring for why it is faithful). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.IsDNS1123Subdomain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace validation

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary.** `IsDNS1123Subdomain(value)` (`validation.go`) returns a new slice of error messages
(`nil` if `value` is a DNS-1123 subdomain): a length check and a precompiled regular expression
(`dns1123SubdomainRegexp`, a package variable that its initializer sets and nothing writes). No
panic for any string. -/
axiom IsDNS1123Subdomain.wp_proof : IsDNS1123Subdomain.spec (GF := GF) (hG := hG)

end proof

end validation
end EtcdGrove
end Perennial
