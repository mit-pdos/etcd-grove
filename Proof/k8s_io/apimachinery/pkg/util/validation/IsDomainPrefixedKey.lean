/-
`validation.IsDomainPrefixedKey(fldPath, key)` (apimachinery, names only): **the trust boundary**.
The axiom (see its docstring for why it is faithful). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.IsDomainPrefixedKey

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
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- **The trust boundary.** `IsDomainPrefixedKey(fldPath, key)` (`validation.go`) checks `key` against a regular
expression and DNS-1123 rules and returns a new `field.ErrorList` (a slice of `*field.Error`) of
the violations, `nil` if none; it builds the errors with `fldPath.String()`, which reads the path
the caller made with `field.NewPath` (read-only, a fresh path). No panic for any key. Each error is
`field.Required(fldPath, "")` or `field.Invalid(fldPath, key, msg)`: a fresh `*field.Error` of type
`FieldValueRequired`/`FieldValueInvalid` whose bad value is a string (`""`, `key`), which nothing
writes after (`field.errorOk`, read-only: the caller gets no write permission). -/
axiom IsDomainPrefixedKey.wp_proof : IsDomainPrefixedKey.spec (GF := GF) (hG := hG)

end proof

end validation
end EtcdGrove
end Perennial
