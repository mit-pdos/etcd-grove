/-
`(*Revision).Run` (`revision.go`; etcd#18472 waits `rc.interval` instead of the constant
`revInterval`). Lean-first (no Rocq counterpart).
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

/-- `rc.Run()` starts the compactor's goroutine and returns. The goroutine, until `rc`'s context
is done, waits on `rc.clock.After(d)` only at `d = P.interval` (the clock is taken at
`D := (· = P.interval)`: etcd#18472's configured interval, or its 5-minute default, never another
duration), skipping a round while paused, and whenever it compacts, it calls
`rc.c.Compact(rc.ctx, &CompactionRequest{Revision: r})` (non-physical) under `rvCompactOk`'s
precondition: `r > 0`; `r + retention = v` for a `v` the revision getter returned (`R v`: the
compaction keeps the last `retention` revisions); and `r` not the last revision that compacted
(or was already compacted), the one `T` records (`T 0` to start). Nothing is said about
termination. `mvcc.ErrCompacted` is a pointer error (`v3cErrCompacted`), the logger is non-nil
and the retention non-negative (a negative one is accepted by `embed` today:
`issues/etcd-compaction-retention-duration.md`). -/
abbrev v3compactor.Revision.Run.spec : Prop :=
  ∀ (rc : Loc) (P : RVParams) (R T : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isRevision rc P ∗ v3cErrCompacted ∗ clockwork.isClockFor P.clock (· = P.interval) ∗
      v3cRevOk P.rg R ∗ rvCompactOk P.c R T P.retention ∗ T (W64 0) ∗
      ⌜P.lg ≠ null ∧ 0 ≤ sint.Z P.retention⌝ }}
    (App (Val (rc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
