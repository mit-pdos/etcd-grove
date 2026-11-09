/-
## `rate.NewLimiter(r, b)`: assumed

**Users.** `startPeer` (`rafthttp/peer.go:216,227`). Snippet: `rate.go` (`ReqDialRetry`).
**Assumed** (`rate.go:69-75`): a struct literal, any `r` and `b`. **Changes.** From `specs-ref`'s
`NewLimiter.lean`. **Margin.** None.
-/
module

public import Spec.golang_org.x.time.rate.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rate

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **A rate limiter.** -/
def NewLimiter.spec : Prop :=
  ∀ (r b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
    (App (App (Val (@! golang_org.x.time.rate.NewLimiter)) (Val #r)) (Val #b))
  {{ (rl : Loc), RET #rl; limiterOk rl }}

end spec
end Rate
end EtcdGrove
end Perennial
