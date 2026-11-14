/-
`v.Infof(format, args...)` (names-only): logging, a no-op for the store's results. The trust
boundary: an axiom, `Proof/k8s_io/klog/v2/Verbose__Infof.lean`. Lean-first (no Rocq counterpart).

**Restricted to the arguments klog formats returning** (klog-args-fix, 2026-11-14,
`notes/klog-args-fix.md`), as `klog.Errorf`'s (`Spec/k8s_io/klog/v2/Errorf.lean`): an enabled
`Verbose` (`-v` at least its level) formats them with the same `fmt.Fprintf`
(`loggingT.printfDepth`), which recovers no panic; until then the spec took any arguments, which Go
refutes (`examples/premisefix/klogargs`, `TestInfofNestedPanicEscapes`). Now the arguments' slice,
at any fraction, and the arguments `klog.argsOk` under the format, both given back.
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
abbrev klog.Verbose.Infof.spec : Prop :=
  ∀ (v : k8s_io.klog.v2.Verbose) (f : GoString) (args : GoSlice) (xs : List GoInterface)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ args ↦*{dq} xs ∗ klog.argsOk f xs }}
    (App (App (Val (v @!! k8s_io.klog.v2.Verbose.ty @!! go!"Infof")) (Val #f)) (Val #args))
  {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}

end spec

end EtcdGrove
end Perennial
