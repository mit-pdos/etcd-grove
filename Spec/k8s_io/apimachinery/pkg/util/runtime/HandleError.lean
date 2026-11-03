/-
`utilruntime.HandleError(err)` (names-only: the trust boundary). Lean-first; for the DaemonSet
controller (`processNextWorkItem`, `syncNodes`' goroutines). It logs the error through the
package's error handlers (rate-limited) and returns. **A boundary spec, pending approval** (the
autoverify run's report, track B): no proof discharges it until the closed theorem's trust base
lists it.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.runtime.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `HandleError(err)`: returns. -/
abbrev utilruntime.HandleError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.runtime.HandleError)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
