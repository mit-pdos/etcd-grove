/-
`s.waitAppliedIndex()` (`v3_server.go`), names only: a trust-boundary contract. Lean-first (no Rocq counterpart); the
lease-renew plan (`notes/lease-renew-plan.md`, 2026-11-01), vocabulary `LeaseRead.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.waitAppliedIndex()`** (names-only, a contract; the lease-renew plan's C3), any goroutine,
with the request side's and the read side's server facts: `nil`, or `ErrStopped` or
`ErrTimeoutWaitAppliedIndex` (`applyErrIs`).

**Why it is faithful.** A `select` over `s.ApplyWaitCommit()` (a channel of the applied-index wait
registry), `s.stopping` and `time.After(applyTimeout)`: `nil`, `errors.ErrStopped` or
`errors.ErrTimeoutWaitAppliedIndex` (the `etcdserver/errors` package's `errors.New` values,
whose `applyErrIs` its initializer gives). It writes nothing the model sees. -/
abbrev EtcdServer.waitAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"waitAppliedIndex")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err) }}

end spec

end EtcdGrove
end Perennial
