/-
`klog.Errorf(format, args...)` (names-only; 2026-11-04, K4 of `notes/k8s-compactor-plan.md`: Kubernetes' compactor loop logs a failed round): logging, a no-op for the compactor's results. The trust boundary: an axiom, `Proof/k8s_io/klog/v2/Errorf.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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
  ∀ (f : GoString) (args : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }}
    (App (App (Val (@! k8s_io.klog.v2.Errorf)) (Val #f)) (Val #args))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
