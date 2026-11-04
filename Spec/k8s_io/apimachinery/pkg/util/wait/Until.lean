/-
`wait.Until(f, period, stopCh)` (names only; `JitterUntil(f, period, 0.0, true, stopCh)`):
calls `f()` on the calling goroutine, again and again, a period apart, until `stopCh` is closed,
then returns. The trust boundary; Lean-first, track C of the DaemonSet run. `R` as
`UntilWithContext.lean`'s; the stop channel a context's `Done()` channel (`informers.doneChOk`).
-/
module

public import Proof.k8s_io.client_go.informers.Defs
public import GeneratedProof.k8s_io.apimachinery.pkg.util.wait

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- `wait.Until(f, period, stopCh)`: see the file header. -/
abbrev wait.Until.spec : Prop :=
  ∀ (f : GoFunc) (period : time.Duration) (ch : GoChan) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait ∗
      informers.doneChOk ch ∗ R ∗
      □ (∀ Φ : val → IProp GF, R -∗ ▷ (R -∗ Φ #()) -∗ WP (App (Val #f) (Val #())) {{ Φ }}) }}
    (App (App (App (Val (@! k8s_io.apimachinery.pkg.util.wait.Until)) (Val #f)) (Val #period))
      (Val #ch))
  {{ RET #(); R }}

end spec

end EtcdGrove
end Perennial
