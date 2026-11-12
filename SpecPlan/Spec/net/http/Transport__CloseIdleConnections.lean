/-
## `(*http.Transport).CloseIdleConnections()` (net/http's trust boundary: assumed)

Why true: closes the idle connections of the transport's pool; requests in flight are not affected
(their connections are not idle). Callable at any time on a round tripper from rafthttp's constructors
(a `*http.Transport`).
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

/-- Closes the idle connections. -/
def Transport.CloseIdleConnections.spec : Prop :=
  ∀ (tr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ roundTripperOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.net.http.Transport.ty) #tr) }}
    (App (Val (tr @!! go.GoType.PointerType _root_.Perennial.net.http.Transport.ty @!! go!"CloseIdleConnections")) (Val #()))
  {{ RET #(); True }}

end spec
end Http
end EtcdGrove
end Perennial
