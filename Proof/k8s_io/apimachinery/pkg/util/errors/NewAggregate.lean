/-
`utilerrors.NewAggregate(errlist)` (`k8s.io/apimachinery/pkg/util/errors/errors.go`; names only in
the translation): the trust-boundary axiom of its spec (`Spec/.../util/errors/NewAggregate.lean`,
until now a named hypothesis of its one user), for conditional authorization's proofs (the union
builder's and the evaluation's aggregated errors). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary.** Go's `NewAggregate(errlist)` (`errors.go`) returns `nil` for an empty
list or one holding only `nil`s, else an `aggregate` (a new slice of the non-`nil` errors); it reads
the list's elements and compares each with `nil` (an interface comparison, no method call), keeps no
reference to the list, and does not panic. The spec says only that some error comes back and the
list is unchanged. -/
axiom NewAggregate.wp_proof : NewAggregate.spec (GF := GF) (hG := hG)

end proof

end utilerrors
end EtcdGrove
end Perennial
