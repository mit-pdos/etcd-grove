/-
## `http.NewServeMux()` (net/http's trust boundary: assumed)

Why true: a new, empty `ServeMux`.
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

/-- **A new mux**, no pattern yet. -/
def NewServeMux.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ True }}
    (App (Val (@! _root_.Perennial.net.http.NewServeMux)) (Val #()))
  {{ (m : Loc), RET #m; muxOwn m [] }}

end spec
end Http
end EtcdGrove
end Perennial
