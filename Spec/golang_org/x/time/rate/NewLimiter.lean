/-
`rate.NewLimiter`: the trust boundary (`golang.org/x/time/rate` is names-only; rafthttp stage 6b,
the peer's stream readers' dial limiters). Lean-first.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`rate.NewLimiter(r, b)`**: a rate limiter (`rate.limiterOk`). -/
abbrev rate.NewLimiter.spec : Prop :=
  ∀ (r b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
    (App (App (Val (@! _root_.Perennial.golang_org.x.time.rate.NewLimiter)) (Val #r)) (Val #b))
  {{ (rl : Loc), RET #rl; rate.limiterOk rl }}

end spec

end EtcdGrove
end Perennial
