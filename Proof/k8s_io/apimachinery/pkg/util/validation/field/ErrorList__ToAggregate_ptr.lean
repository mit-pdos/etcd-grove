/-
`(*field.ErrorList).ToAggregate()` (apimachinery, names only): **the trust boundary**, a local
workaround for a goose limitation. The axiom (see its docstring for why it is faithful). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary (a workaround).** The Go spec puts `ErrorList`'s value methods in the
method set of `*ErrorList`: `l.ToAggregate()` with `l : *ErrorList` is `(*l).ToAggregate()`. So
the call loads the slice header `*l` (read only, kept at its fraction) and runs the value method on
it. The axiom is stated over the value method's spec (`ErrorList.ToAggregate.spec`, a hypothesis;
its own trust-boundary axiom is `ErrorList.ToAggregate.wp_proof`): it says only "load, then that
spec", nothing about `ToAggregate`'s behaviour.
Goose states this pointer wrapper for every translated type as `ptr_M_unfold`
(`MethodUnfold (ptr T) M (λ r, MethodResolve T M (load T r))`, independent of `M`'s body, e.g.
`authorizer.ptr_IsAllow_unfold`), but skips it for an axiomatized (names-only) method together with
`M_unfold`. To retire once goose emits `ptr_M_unfold` for axiomatized value-receiver methods (then
this is a lemma, proved like `sets.Set.wp_ptr_Has_of`); see `notes/perennial-changes.md`. -/
axiom ErrorList.ToAggregate_ptr.wp_proof
    (wp_ToAggregate : ErrorList.ToAggregate.spec (GF := GF) (hG := hG)) :
    ErrorList.ToAggregate_ptr.spec (GF := GF) (hG := hG)

end proof

end field
end EtcdGrove
end Perennial
