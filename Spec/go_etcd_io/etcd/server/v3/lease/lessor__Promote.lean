/-
`(*lessor).Promote` (`server/lease/lessor.go`; proved over its body since prove-ps2-promote,
2026-11-21). Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Promote(extend)` (write-locked): makes the lessor primary (a fresh `demotec`), refreshes
every lease's expiry, registers it with the expiry notifier and schedules its checkpoint, and
spreads out the expiries of piled-up leases (float arithmetic, a float-to-integer conversion,
`sort.Sort` of the leases by `Remaining()`, which read-locks each lease's `expiryMu`); it touches
only the lessor's memory under its lock. It indexes the sorted leases' first only when there are
at least `leaseRevokeRate` of them, which `lessorCfg` makes positive (audit B4b, 2026-10-18: a
negative rate with no lease panics; until then the configuration's rate was unconstrained). Its
checkpoint scheduling logs (`scheduleCheckpointIfNeeded`'s `le.lg.Debug`, under `le.lg != nil`)
through `lessorCfg`'s logger, nil or a zap logger (`zapLoggerOk`; 2026-11-10, the user's decision
of 2026-11-07, sweep B3-2: until then unconstrained, and a zero `&zap.Logger{}` panicked here).
(prove-ps2-lease, 2026-11-21) Its `le.demotec = make(chan struct{})` (`lessor.go:484`, under the write
lock) keeps `demotec`'s ghost state (`lessorExtra`'s `demoteTie`, InvLessor.lean): the fresh channel
is idle and owned (`chan.wp_make1`); a fresh token `γt` and `onceChanInv` at `.Idle` are
allocated, and around the store (one atomic step) the invariant `demoteOuter` is opened, the ghost
variable (half the lock's, held whole under the write lock, half the invariant's) set to the new
channel, and its token put in; the old channel's token, if a previous `Promote` left one, is
dropped (no `Demote` in between: that channel is never closed, which only leaves a receiver of it
blocked). Ghost state only: no Go behavior is assumed for it.
(prove-ps2-promote, 2026-11-21; ledger 2026-11-21, "the lessor's `Promote` lacks the resources its
sort's `Remaining()` takes") With `leaseRevokeRate` or more leases it sorts them
(`leasesByExpiry`, whose `Less` calls `Remaining()`) and calls `Remaining()` on each, each a read
lock of the lease's `expiryMu`, a reader slot borrowed from the lease's leveled pool: so, as
`Leases`, it takes the level-0 token (`levelTok lessorLvl`, given back), at most `2^30 - 1` live
threads, and `receiptBound GF ≤ 2^62` (the sort takes at most `2^62` elements; the lease map is
smaller than the receipts' bound). Until then the axiom took neither. -/
abbrev lease.lessor.Promote.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ levelTok lessorLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      ⌜receiptBound GF ≤ 2 ^ 62⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Promote")) (Val #d))
  {{ RET #(); levelTok lessorLvl }}

end spec

end EtcdGrove
end Perennial
