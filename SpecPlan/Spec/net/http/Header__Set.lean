/-
## `http.Header.Set(key, value)` (net/http's trust boundary: assumed)

Why true: `textproto.MIMEHeader.Set` of the canonical key replaces its values by `[value]`.
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

/-- **Sets a header** of an owned map. -/
def Header.Set.spec : Prop :=
  ∀ (hm : GoMap) (hs : List (GoString × GoString)) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ hdrMap hm hs }}
    (App (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Set")) (Val #k)) (Val #v))
  {{ RET #(); hdrMap hm (hdrSet hs k v) }}

end spec
end Http
end EtcdGrove
end Perennial
