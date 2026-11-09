/-
## `net.Listener.Close()` (net/http's trust boundary: assumed)

Why true: closing a listener (from any goroutine, any number of times: later calls return an
error) makes its `Accept`, and so the `Serve` on it, return.
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

/-- **Closes a listener.** -/
def Listener.Close.spec : Prop :=
  ∀ (l : GoInterface) (i : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜l = interface.ok i⌝ ∗ listenerCloser l }}
    (App (Val #(methods i.ty go!"Close" i.v)) (Val #()))
  {{ (err : GoInterface), RET #err; errOk err }}

end spec
end Http
end EtcdGrove
end Perennial
