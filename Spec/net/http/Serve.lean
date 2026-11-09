/-
## `http.Serve(l, h)` (net/http's trust boundary: assumed)

Why true: `Serve` accepts connections on `l` and serves each on its own goroutine (`go c.serve(ctx)`),
reading requests and calling `h.ServeHTTP` for each with a fresh `*response` (an `http.Flusher`)
and the request as read; a handler's panic is recovered (`conn.serve`'s deferred `recover`), the
connection dropped. By the closed world (the header of `Api.lean`) every request read at `a` was
sent by a client of the program through `RoundTrip` to `a`, so the handler gets what that client
proved under `P` (and its ticket for a `onceOnly` request, which Go's client sends once). The
handler goroutines are the trusted model's forks: their thread tokens come from the thread fuel.
It returns only with an error (the listener closed or failed).
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

/-- **Serves `h` on the listener bound at `a`**, whose protocol `P` the caller owns the right to serve; returns only with an error. -/
def Serve.spec : Prop :=
  ∀ (l h : GoInterface) (a : GoString) (P : Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ listenerAt l a ∗ protoOwn a P ∗ handlerOk h P go!"/" }}
    (App (App (Val (@! _root_.Perennial.net.http.Serve)) (Val #l)) (Val #h))
  {{ (err : GoInterface), RET #err; errOk err }}

end spec
end Http
end EtcdGrove
end Perennial
