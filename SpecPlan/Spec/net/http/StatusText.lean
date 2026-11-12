/-
## `http.StatusText(code)` (net/http's trust boundary: assumed)

Why true: a table lookup (`""` for an unknown code).
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

/-- Some string. -/
def StatusText.spec : Prop :=
  ∀ (code : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ True }}
    (App (Val (@! _root_.Perennial.net.http.StatusText)) (Val #code))
  {{ (s : GoString), RET #s; True }}

end spec
end Http
end EtcdGrove
end Perennial
