/-
`utilflowcontrol.WatchInitialized(ctx)` (`k8s.io/apiserver/pkg/util/flowcontrol/apf_context.go:49-53`):
of a context whose value at APF's initialization-signal key is nil or not an `InitializationSignal`
(`flowcontrol.initSignalRes`, k8s 7f-5 T5-b; `k8sctx.k8sCtxOk` has it), returns, calling nothing.
Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.util.flowcontrol.initializationSignalFrom

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

/-- See the file header. -/
abbrev flowcontrol.WatchInitialized.spec : Prop :=
  ∀ (ci : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.flowcontrol ∗
      context.valueAt ci flowcontrol.initSignalKeyAny (flowcontrol.initSignalRes (hG := hG)) }}
    (App (Val (@! k8s_io.apiserver.pkg.util.flowcontrol.WatchInitialized))
      (Val #(GoInterface.ok ci)))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
