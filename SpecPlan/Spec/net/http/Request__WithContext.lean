/-
## `(*http.Request).WithContext(ctx)` (net/http's trust boundary: assumed)

Why true: a shallow copy with the new context (`ctx` non-nil, else Go panics); the header map is
shared, so the original is given up.
-/
module

public import SpecPlan.Spec.net.http.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Http

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The request with a context**: the copy takes the original's place. -/
def Request.WithContext.spec : Prop :=
  ∀ (r : Loc) (R : HReq) (bd ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ reqOwn r R bd ∗ Context.ctxOk ctx }}
    (App (Val (r @!! go.GoType.PointerType _root_.Perennial.net.http.Request.ty @!! go!"WithContext")) (Val #ctx))
  {{ (r' : Loc), RET #r'; reqOwn r' R bd }}

end spec
end Http
end EtcdGrove
end Perennial
