/-
`v3compactor.New(lg, mode, retention, rg, c)` (`compactor.go`): names-only. Lean-first (no Rocq
counterpart); the server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for
`NewServer`; an axiom at the trust boundary since unit N4 (2026-10-17, D14e), why it is true of
the Go code below. `NewServer.spec` takes the compactor off (`AutoCompactionRetention = 0`), so
its proof does not call it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`New(lg, mode, retention, rg, c)`** with a retention of at least 10ns in absolute value:
it returns (a compactor or an error).

Why it is true of the Go code (`compactor.go`, `periodic.go`, `revision.go` at the etcd pin):
`New` makes a periodic compactor (`newPeriodic`: its retention array sized by the period over
the retry interval, `min(period, 1h) / 10`, nonzero for a period of at least 10ns in absolute
value; below, a division by zero: `issues/etcd-compactor-periodic-tiny-retention.md`) or a
revision compactor (no division), or returns an error for another mode; it starts no goroutine
(`Run` does). The compactor's contract (its `Run`'s goroutine proposes compactions through the
server) is not stated. -/
abbrev v3compactor.New.spec : Prop :=
  ∀ (lg : Loc) (mode : GoString) (ret : time.Duration) (rg c : GoInterface),
  sint.Z ret ≤ -10 ∨ 10 ≤ sint.Z ret →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New))
      (Val #lg)) (Val #mode)) (Val #ret)) (Val #rg)) (Val #c))
  {{ (cp err : GoInterface), RET (PairV #cp #err); True }}

end spec

end EtcdGrove
end Perennial
