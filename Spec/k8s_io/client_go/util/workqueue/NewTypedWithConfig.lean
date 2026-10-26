/-
`NewTypedWithConfig[T](config)` (`queue.go`): `newQueueWithConfig(config, 500ms)`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `NewTypedWithConfig(config)` for a configuration the specs cover (`queueConfigOk`: the default
FIFO, no metrics): a typed queue and its shutdown tokens. -/
abbrev NewTypedWithConfig.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (cfg : TypedQueueConfig K),
  queueConfigOk cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val #(functions NewTypedWithConfig [T])) (Val #cfg))
  {{ (q : Loc) (γ : QNames), RET #q; isTyped (K := K) q γ ∗ shutdownToks γ shutdownPool }}

end spec

end workqueue
end EtcdGrove
end Perennial
