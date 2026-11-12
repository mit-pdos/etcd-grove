/-
## `http.Serve(l, h)` (net/http's trust boundary: assumed)

Why true: `Serve` accepts connections on `l` and serves each on its own goroutine, reading
requests and calling `h.ServeHTTP` for each with a fresh `*response` (an `http.Flusher`) and the
request as read; a handler's panic is recovered (`conn.serve`'s deferred `recover`), the connection
dropped. By the closed world (`Api.lean`'s header) every request read on `l` was sent by a client
of the program through `RoundTrip` to a host whose protocol is `a`'s `P`, so the handler gets what
that client proved (and its ticket for a `onceOnly` request, which Go's client sends once). Each
handler run draws a thread token from the caller's pool and returns it at its end (round 1, F1: no
token from nothing; the physical premise, at most `n` concurrent handlers, is the adequacy
theorem's bound on live threads). It returns only with an error (the listener closed or failed);
the pool stays lent to the runs still in flight.
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

/-- **Serves `h` on the listener bound at `a`**, whose protocol is `P`, lending its handler runs the pool's thread tokens; returns only with an error. -/
def Serve.spec : Prop :=
  ∀ (l h : GoInterface) (a : GoString) (P : Proto GF) (p : GName) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ listenerAt l a ∗ protoAt a P ∗ handlerOk h P go!"/" ∗ handlerPool p n }}
    (App (App (Val (@! _root_.Perennial.net.http.Serve)) (Val #l)) (Val #h))
  {{ (err : GoInterface), RET #err; errOk err }}

end spec
end Http
end EtcdGrove
end Perennial
