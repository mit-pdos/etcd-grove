/-
`store.setupMetricsReporter` (`kvstore.go`; translated 2026-10-23, the restore plan's R0, its
globals in R2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.setupMetricsReporter()`: reads `s.b` and sets the five metrics reporters, each under its
lock (`reportVar`, the package's facts; the restore plan's R2). The closures run only from
Prometheus's collector, which no verified code calls, so nothing is said of them. -/
abbrev mvcc.store.setupMetricsReporter.spec : Prop :=
  ∀ (s : Loc) (b : GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dq} b }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"setupMetricsReporter")) (Val #()))
  {{ RET #(); s.[store, go!"b"] ↦{dq} b }}

end spec

end EtcdGrove
end Perennial
