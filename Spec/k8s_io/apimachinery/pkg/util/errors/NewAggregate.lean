/-
`utilerrors.NewAggregate(errlist)` (`k8s.io/apimachinery/pkg/util/errors/errors.go`; names only in
the translation): **the trust boundary, a named hypothesis pending approval**. The code returns
`nil` for an empty list (or one of `nil`s), else an `aggregate` of a new slice holding the
non-`nil` errors (it reads the list's elements, compares each with `nil`, and keeps no reference to
the list). The spec says: some `Aggregate`, the list kept. Lean-first (no Rocq counterpart).
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
abbrev NewAggregate.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (es : List GoInterface),
  {{ (s ↦*{dq} es : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.errors.NewAggregate)) (Val #s))
  {{ (a : GoInterface), RET #a; s ↦*{dq} es }}

end spec

end utilerrors
end EtcdGrove
end Perennial
