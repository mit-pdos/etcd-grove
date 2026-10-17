/-
`(*Periodic).Run` (`periodic.go`; unchanged by etcd#18472, but it calls `getCompactInterval`,
which etcd#18472 changes). Lean-first (no Rocq counterpart).
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

/-- `pc.Run()` starts the compactor's goroutine and returns. The goroutine, until `pc`'s context
is done, samples a revision every `getRetryInterval()`: it waits on `pc.clock.After(d)` only at
`d = pdRetry P.period` (`min(period, 1h) / 10`; the configured `interval` does not change the
sampling), skipping a round while paused, and whenever it compacts, it calls
`pc.c.Compact(pc.ctx, &CompactionRequest{Revision: r})` (non-physical) under `pdCompactOk`'s
precondition: `r` is a revision the getter returned (`R r`; the oldest one in the window) and not
the last revision that compacted (or was already compacted), the one `T` records (`T 0` to
start). When it compacts (the elapsed time since the last success against `period`, then
`getCompactInterval()`) is not stated: Perennial's `Time.Sub` returns some duration. Nothing is
said about termination. Premises: the goroutine gets the revision window (`pdRevs pc []`, as
`newPeriodic` leaves it) and a reader token of `pc.mu`; `mvcc.ErrCompacted` is a pointer error;
the logger is non-nil; the period is at least 10 ns in absolute value (`getRetentions`). -/
abbrev v3compactor.Periodic.Run.spec : Prop :=
  ∀ (pc : Loc) (P : PDParams) (R T : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic pc P ∗ pdReader pc ∗ pdRevs pc [] ∗ v3cErrCompacted ∗
      clockwork.isClockFor P.clock (· = pdRetry P.period) ∗
      v3cRevOk P.rg R ∗ pdCompactOk P.c R T ∗ T (W64 0) ∗
      ⌜P.lg ≠ null ∧ (10 ≤ sint.Z P.period ∨ sint.Z P.period ≤ -10)⌝ }}
    (App (Val (pc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
