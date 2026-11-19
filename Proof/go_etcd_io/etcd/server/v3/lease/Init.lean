/-
Package initialization of `go_etcd_io.etcd.server.v3.lease`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`leaseInit`, `Base.lean`): the error variables `ErrNotPrimary`,
`ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge` (translated `errors.New` calls: leaf pointer errors
without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose `Error()` returns), `forever` (the zero
`time.Time`), the counters `leaseGranted`, `leaseRevoked` and the histogram `leaseTotalTTLs`
(`metrics.go`, untranslated: the trust-boundary axioms `<X>_init`); `opaqueInitsOk` states the
other untranslated initializers run.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.container.heap.Init
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.leasepb.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.Init
public import Proof.go_uber_org.zap.Init
public import Proof.errors.NewVarCell
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.server.v3.lease
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.lease`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([defaultLeaseRevokeRate.init,
        leaseCheckpointRate.init,
        defaultLeaseCheckpointInterval.init,
        maxLeaseCheckpointBatchSize.init,
        defaultExpiredleaseRetryInterval.init,
        leaseRenewed.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.lease`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `leaseGranted = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`, whose `Inc` returns. -/
axiom leaseGranted_init :
    {{ (True : IProp GF) }} (App (Val leaseGranted.init) (Val #()))
    {{ RET #(); ∃ c : GoInterfaceOk, globalAddr leaseGranted ↦ GoInterface.ok c ∗ counterSpec c }}

/-- `leaseRevoked = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`, whose `Inc` returns. -/
axiom leaseRevoked_init :
    {{ (True : IProp GF) }} (App (Val leaseRevoked.init) (Val #()))
    {{ RET #(); ∃ c : GoInterfaceOk, globalAddr leaseRevoked ↦ GoInterface.ok c ∗ counterSpec c }}

/-- `leaseTotalTTLs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom leaseTotalTTLs_init :
    {{ (True : IProp GF) }} (App (Val leaseTotalTTLs.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr leaseTotalTTLs ↦ GoInterface.ok h ∗ go_etcd_io.etcd.server.v3.storage.backend.histSpec h }}

end go_etcd_io.etcd.server.v3.lease
end opaqueInits

end Perennial
