/-
`v.InfoS(msg, keysAndValues...)` (klog, names-only): structured logging, a no-op for the watcher's
results. **Candidate trust-boundary text, NOT an axiom** (k8s 7f-5a-P, 2026-11-15): stated so that
`blockLogger.recordWait`'s proof can take it as a callee hypothesis, as `parseEvent`'s takes
`mvccpb.Event_EventType.StringPtr.spec`; whether it becomes an axiom (and in what form) is for
etcd-grove-81's axiom review. Restricted to the call shape the watcher makes
(`block_logger.go:69-75`): keys and values whose dynamic types are `string`, `int`,
`time.Duration` or `schema.GroupResource` (klog's text serializer formats them through
`fmt`/`String()`, which return for these types). Lean-first (no Rocq counterpart).
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

/-- A key or value `InfoS` is given by the watcher's block logger: a `string`, an `int`, a
`time.Duration` or a `schema.GroupResource`. -/
def klog.infoSArgOk (x : GoInterface) : Prop :=
  ∃ ii : GoInterfaceOk, x = GoInterface.ok ii ∧
    ii.ty ∈ [go.string, go.int, _root_.Perennial.time.Duration.ty,
      k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty]

/-- See the file header. -/
abbrev klog.Verbose.InfoS.spec : Prop :=
  ∀ (v : k8s_io.klog.v2.Verbose) (msg : GoString) (args : GoSlice) (xs : List GoInterface)
    (dq : DFrac),
  (∀ x ∈ xs, klog.infoSArgOk x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ args ↦*{dq} xs }}
    (App (App (Val (v @!! k8s_io.klog.v2.Verbose.ty @!! go!"InfoS")) (Val #msg)) (Val #args))
  {{ RET #(); args ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
