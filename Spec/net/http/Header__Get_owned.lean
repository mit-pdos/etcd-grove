/-
## `http.Header.Get(key) (an owned map)` (net/http's trust boundary: assumed)

Why true: as `Header.Get`; on a map being built.
-/
module

public import Spec.net.http.Api

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

/-- **Reads a header** of an owned map. -/
def Header.Get_owned.spec : Prop :=
  ∀ (hm : GoMap) (hs : List (GoString × GoString)) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ hdrMap hm hs }}
    (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Get")) (Val #k))
  {{ RET #(hdrGet hs k); hdrMap hm hs }}

end spec
end Http
end EtcdGrove
end Perennial
