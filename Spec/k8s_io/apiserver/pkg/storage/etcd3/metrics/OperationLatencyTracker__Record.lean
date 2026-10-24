/-
`t.Record(err, startTime)` (the store's latency metrics, names-only): a no-op for its results. The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/OperationLatencyTracker__Record.lean`. Lean-first (no Rocq
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev metrics.OperationLatencyTracker.Record.spec : Prop :=
  ∀ (t : Loc) (err : GoInterface) (start : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics ∗ ⌜t ≠ null⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.metrics.OperationLatencyTracker.ty @!! go!"Record"))
      (Val #err)) (Val #start))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
