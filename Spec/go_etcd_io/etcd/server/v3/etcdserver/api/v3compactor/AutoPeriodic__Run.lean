/-
`v3compactor.AutoPeriodic.Run` (`autoperiodic.go`, etcd#22095: the sampling loop). Lean-first
(no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [f2i : Float64ToInt64] [f2i_sem : Float64ToInt64Semantics]
/-- `ac.Run()` starts the compactor's goroutine and returns. The goroutine, until `ac`'s context
is done, samples every `AutoPeriodicSampleInterval` (of `ac`'s clock), skipping a sample while
paused, and whenever it compacts, it calls `ac.c.Compact(ac.ctx, &CompactionRequest{Revision:
r})` (non-physical) under `apCompactOk`'s precondition: `r > 0`; `r + retention = v` for a `v`
the revision getter returned (`R v`: the store was at revision at least `v`, so the compaction
keeps the last `retention` revisions); and `r` above the last revision that compacted (or was
already compacted), the one `T` records (`T 0` to start). Nothing is said about when it
compacts (the projection is over opaque floats: `shouldCompact`'s spec) nor about its
termination. The tuning variables are read-only (`apTuning`), `mvcc.ErrCompacted` is a pointer
error (`apErrCompacted`), the logger is non-nil and the retention non-negative (what
`embed`'s `parseCompactionRetention` gives for an integer; a negative duration retention
does not meet it: see the report of etcd#22095). Float-to-integer conversions step by
`Float64ToInt64Semantics` (a model assumption: Perennial has none). -/
abbrev v3compactor.AutoPeriodic.Run.spec : Prop :=
  ∀ (ac : Loc) (P : APParams) (tv : APTuning) (R T : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isAutoPeriodic ac P ∗ apTuning tv ∗ apErrCompacted ∗ apClockOk P.clock ∗
      apSizeOk P.sg ∗ apRevOk P.rg R ∗ apCompactOk P.c R T P.retention ∗ T (W64 0) ∗
      ⌜P.lg ≠ null ∧ 0 ≤ sint.Z P.retention⌝ }}
    (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
