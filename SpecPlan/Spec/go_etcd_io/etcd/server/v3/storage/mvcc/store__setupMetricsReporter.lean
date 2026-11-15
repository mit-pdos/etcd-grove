/-
`(*store).setupMetricsReporter()` (`kvstore.go:521`). Internal: `restore`. Sets the package's
reporter closures under their mutexes (the mutexes' invariants: the package's initialization,
`isPkgInit`); the closures, called by Prometheus' collector outside the model, are not specified.

**Changes** from `specs-ref`'s file: unchanged in substance (namespace `Mvcc`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.setupMetricsReporter()`: reads `s.b`; no panic. -/
def store.setupMetricsReporter.spec : Prop :=
  ∀ (s : Loc) (b : GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dq} b }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"setupMetricsReporter")) (Val #()))
  {{ RET #(); s.[store, go!"b"] ↦{dq} b }}

end spec
end Mvcc
end EtcdGrove
end Perennial
