/-
`wait.UntilWithContext(ctx, f, period)` (names only; `JitterUntilWithContext(ctx, f, period,
0.0, true)`): calls `f(ctx)` on the calling goroutine, again and again, a period apart, until
`ctx` is done (checked before each call and while waiting), then returns. Each call is wrapped
in `func() { defer runtime.HandleCrash(); f(ctx) }()`, which re-panics. The trust boundary;
Lean-first, track C of the DaemonSet run.

The caller's `R` is the loop's resource (a worker's thread token): every call of `f` takes it and
gives it back. `f` runs any number of times, including none.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import GeneratedProof.k8s_io.apimachinery.pkg.util.wait
public import Perennial.Proof.context.Base

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
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- `wait.UntilWithContext(ctx, f, period)`: see the file header. -/
abbrev wait.UntilWithContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (f : GoFunc)
    (period : time.Duration) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait ∗
      context.isContext ctx cs ∗ R ∗
      □ (∀ Φ : val → IProp GF, R -∗ ▷ (R -∗ Φ #()) -∗
          WP (App (Val #f) (Val #(GoInterface.ok ctx))) {{ Φ }}) }}
    (App (App (App (Val (@! k8s_io.apimachinery.pkg.util.wait.UntilWithContext))
      (Val #(GoInterface.ok ctx))) (Val #f)) (Val #period))
  {{ RET #(); R }}

end spec

end EtcdGrove
end Perennial
