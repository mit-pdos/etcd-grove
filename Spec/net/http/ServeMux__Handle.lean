/-
## `(*http.ServeMux).Handle(pattern, h)` (net/http's trust boundary: assumed)

Why true: `Handle` registers `pattern` (Go panics on an empty pattern, a `nil` handler or a
pattern already registered: the premises). The rafthttp handler's patterns are distinct literals.
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

/-- **Registers a handler** for a new, non-empty pattern. -/
def ServeMux.Handle.spec : Prop :=
  ∀ (m : Loc) (L : List (GoString × GoInterface)) (pat : GoString) (h : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ muxOwn m L ∗ ⌜pat ≠ [] ∧ h ≠ interface.nil ∧ ∀ h', (pat, h') ∉ L⌝ }}
    (App (App (Val (m @!! go.GoType.PointerType _root_.Perennial.net.http.ServeMux.ty @!! go!"Handle")) (Val #pat)) (Val #h))
  {{ RET #(); muxOwn m (L ++ [(pat, h)]) }}

end spec
end Http
end EtcdGrove
end Perennial
