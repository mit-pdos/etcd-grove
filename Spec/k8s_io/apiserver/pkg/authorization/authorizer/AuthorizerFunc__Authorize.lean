/-
`f.Authorize(ctx, a)` (`interfaces.go`): `f(ctx, a)`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. -/
abbrev AuthorizerFunc.Authorize.spec : Prop :=
  ∀ (f : GoFunc) (ctx a : GoInterface),
  {{ authzFnOk (GF := GF) f }}
    (App (App (Val (f @!! AuthorizerFunc.ty @!! go!"Authorize")) (Val #ctx)) (Val #a))
  {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); True }}

end spec

end authorizer
end EtcdGrove
end Perennial
