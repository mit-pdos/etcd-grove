/-
# `golang.org/x/time/rate`: the trust boundary (batch 4b)

x/time/rate is translated types and names only: **assumed**, true of its `rate.go` at the pin. A
`Limiter` is safe for concurrent use (every method takes its mutex), so it is a persistent fact.

* `limiterOk rl` (opaque, persistent): `rl` is a `*Limiter` made by `NewLimiter`.
* `reservationOk r` (opaque, persistent): `r` is a `*Reservation` made by `Reserve`.

Users: rafthttp's dial-retry limiters (`peer.go:216,227`: `NewLimiter(t.DialRetryFrequency, 1)`;
`stream.go:449`: `cr.rl.Wait(cr.ctx)`; `transport.go:153`: `Every(100ms)`); client-go's bucket rate
limiter (Kubernetes' workqueue: `Reserve().Delay()`). Snippet: `examples/specreq/pkgleaves/rate.go`
(`ReqDialRetry`).

Left out: `AllowN`, `ReserveN`, `DelayFrom` (client-go's other limiters; no spec needed so far).
-/
module

public import GeneratedProof.golang_org.x.time.rate
public import Spec.PkgInit.golang_org.x.time.rate
public import Spec.context.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rate

open Iris Iris.BI

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`rl` is a rate limiter** (persistent). -/
opaque limiterOk (rl : Loc) : IProp GF := iprop(True)

/-- **`r` is a reservation** (persistent). -/
opaque reservationOk (r : Loc) : IProp GF := iprop(True)

def limiterOk_persistent.spec : Prop := ∀ rl, Persistent (limiterOk (GF := GF) rl)
def reservationOk_persistent.spec : Prop := ∀ r, Persistent (reservationOk (GF := GF) r)

end vocab

end Rate
end EtcdGrove
end Perennial
