/-
`(*Reflector).resyncChan()` (`reflector.go:445`): with resync period `0`, a `nil` channel (nothing
is ever sent on it) and a cleanup function returning `false`. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round. Stated for resync period `0`, as `Main`'s informers.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefInf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel informer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The cleanup function** returns `false` (persistent). -/
def cleanupOk (cf : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #false -∗ WP (App (Val #cf) (Val #())) {{ Φ }})

instance cleanupOk_persistent (cf : GoFunc) : Persistent (cleanupOk (GF := GF) cf) := by
  unfold cleanupOk; infer_instance

/-- **`r.resyncChan()`** with resync period `0`: a `nil` channel, a cleanup returning `false`. -/
abbrev Reflector.resyncChan.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      r.[Reflector, go!"resyncPeriod"] ↦□ (W64 0 : time.Duration) }}
    (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"resyncChan")) (Val #()))
  {{ (cf : GoFunc), RET (PairV #chan.nil #cf); cleanupOk cf }}

end spec

end cache
end EtcdGrove
end Perennial
