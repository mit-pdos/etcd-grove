/-
`ReportEventReceived` (`metrics.go`, names-only: the trust boundary). Lean-first (no Rocq
counterpart); D19j (2026-10-18: until then the package fact `reportEventOk` of the watch path,
stated for every `n`).
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

/-- `ReportEventReceived(n)` of a non-negative `n` returns: `pendingEventsGauge.Sub(float64(n))`
and `totalEventsCounter.Add(float64(n))` (prometheus metrics; a counter's `Add` panics on a
negative value, hence `0 ≤ n`: the watch server passes `len(...)` of an event slice). -/
abbrev mvcc.ReportEventReceived.spec : Prop :=
  ∀ n : w64, 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) (Val #n))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
