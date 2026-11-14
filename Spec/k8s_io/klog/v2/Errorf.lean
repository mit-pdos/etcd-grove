/-
`klog.Errorf(format, args...)` (names-only; 2026-11-04, K4 of `notes/k8s-compactor-plan.md`:
Kubernetes' compactor loop logs a failed round): logging, a no-op for the compactor's results. The
trust boundary: an axiom, `Proof/k8s_io/klog/v2/Errorf.lean`. Lean-first (no Rocq counterpart).

**Restricted to the arguments klog formats returning** (klog-args-fix, 2026-11-14,
`notes/klog-args-fix.md`): until then the spec took any format and any arguments, which Go refutes
(`examples/premisefix/klogargs`): klog formats them with `fmt.Fprintf` and recovers no panic, so an
argument whose `Error()` panics with a value whose `String()` panics escapes, and a map written
concurrently makes the runtime throw. Now the arguments' slice, at any fraction, and the arguments
`klog.argsOk` under the format (`Spec/k8s_io/klog/v2/Args.lean`), both given back. What klog does
beyond formatting (with its default flags, `logtostderr`, and no `SetLogFilter`: the line written
to standard error, a failed write ignored) is the boundary's assumption, as before.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Spec.k8s_io.klog.v2.Args

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
abbrev klog.Errorf.spec : Prop :=
  ∀ (f : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ args ↦*{dq} xs ∗ klog.argsOk f xs }}
    (App (App (Val (@! k8s_io.klog.v2.Errorf)) (Val #f)) (Val #args))
  {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}

end spec

end EtcdGrove
end Perennial
