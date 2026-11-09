/-
## `net.Listen(network, address) (net's, as this boundary uses it)` (net/http's trust boundary: assumed)

Why true: the bind of a TCP socket at `address`, or an error (in use, not permitted). The
socket is bound at `address` itself, unless its port is `0`: then at the port the kernel chose,
whose string `l.Addr()` reports. A fresh listener each time (a closed socket's port may be bound
again).
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

/-- **Binds a listener** at `address` (or its actual address for port `0`), or fails. -/
def Listen.spec : Prop :=
  ∀ (network address : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ True }}
    (App (App (Val (@! _root_.Perennial.net.Listen)) (Val #network)) (Val #address))
  {{ (l : GoInterface) (err : GoInterface), RET (PairV #l #err); (⌜err ≠ interface.nil⌝ ∗ errOk err) ∨ (⌜err = interface.nil⌝ ∗ ∃ a, listenerAt l a ∗ listenerCloser l ∗ ⌜¬ portZero address → a = address⌝) }}

end spec
end Http
end EtcdGrove
end Perennial
