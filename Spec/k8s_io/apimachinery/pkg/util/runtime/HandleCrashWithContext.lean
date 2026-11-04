/-
`utilruntime.HandleCrashWithContext(ctx, additionalHandlers...)` (names only): a deferred
crash handler; with no panic in flight (`recover()` returns `nil`) it returns. The trust boundary
(as `HandleCrashWithLogger.lean`); Lean-first, track C of the DaemonSet run.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import GeneratedProof.k8s_io.apimachinery.pkg.util.runtime

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


/-- `HandleCrashWithContext(ctx, handlers...)` with no panic in flight: returns. -/
abbrev utilruntime.HandleCrashWithContext.spec : Prop :=
  ∀ (ctx : GoInterface) (hs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithContext)) (Val #ctx))
      (Val #hs))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
