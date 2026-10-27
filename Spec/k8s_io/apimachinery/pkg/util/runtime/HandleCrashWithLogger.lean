/-
`utilruntime.HandleCrashWithLogger(logger, additionalHandlers...)` (names-only: the trust
boundary). Lean-first; for client-go's delaying queue (`defer
utilruntime.HandleCrashWithLogger(logger)` in `waitingLoop`). It `recover()`s: with no panic in
flight it returns (with one it logs and, by default, panics again: the proof shows the loop does
not panic, so only that case is stated).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.runtime.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `HandleCrashWithLogger(logger, handlers...)` with no panic in flight: returns. -/
abbrev utilruntime.HandleCrashWithLogger.spec : Prop :=
  ∀ (l : github_com.go_logr.logr.Logger) (hs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithLogger)) (Val #l)) (Val #hs))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
