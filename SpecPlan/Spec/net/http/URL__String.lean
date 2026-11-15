/-
## `url.URL.String() (net/url, as this boundary uses it)` (net/http's trust boundary: assumed)

Why true: `String` assembles the URL's fields with escaping and never panics; its result is `urlStr u` (opaque).
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

/-- **The URL's string.** -/
def URL.String.spec : Prop :=
  ∀ (u : _root_.Perennial.net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ True }}
    (App (Val (u @!! _root_.Perennial.net.url.URL.ty @!! go!"String")) (Val #()))
  {{ RET #(urlStr u); True }}

end spec
end Http
end EtcdGrove
end Perennial
