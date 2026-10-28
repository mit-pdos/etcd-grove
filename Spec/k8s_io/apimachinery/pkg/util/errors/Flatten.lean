/-
`utilerrors.Flatten(agg)` (`k8s.io/apimachinery/pkg/util/errors/errors.go`; names only in the
translation): **the trust boundary, a named hypothesis pending approval**. The code returns `nil`
for a `nil` aggregate, else a new aggregate of the non-`nil` errors of `agg` with nested
aggregates flattened (`agg.Errors()`, comma-ok type assertions, `NewAggregate`), reading only the
aggregate's own (immutable) slices. The spec says: some `Aggregate`. Lean-first.
-/
module

public import Proof.k8s_io.kubernetes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev Flatten.spec : Prop :=
  ∀ (a : GoInterface),
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.errors.Flatten)) (Val #a))
  {{ (a' : GoInterface), RET #a'; True }}

end spec

end utilerrors
end EtcdGrove
end Perennial
