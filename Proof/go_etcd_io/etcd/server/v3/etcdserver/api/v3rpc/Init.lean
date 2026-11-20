/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`v3rpcInit`, `Base.lean`): its error map `toGRPCErrorMap` and counter vector
`clientRequests` with its label names (untranslated: the trust-boundary axioms `<X>_init`), `metricsServerLock` (an
unlocked mutex guarding `metricsServerCached`, `nil`: `metricsVars`), `rpctypes`' errors and
metadata keys and `etcdserverpb`'s sort-name maps and six `ServiceDesc`s (`svcDescsOk`, from their
facts), and `context.Canceled` a
pointer error (from the read package's premise `EtcdGrove.ContextReadErrs`: Perennial's `context`
fact lacks it). Its precondition has the read package's registration rights
(`EtcdGrove.read.readRegPerm`, decision D16), which it passes on to `etcdserver`'s initializer.
(D19j, 2026-10-18) And what `watch.go` reads but `io.EOF` (`watchPkgVars`): `auth`'s and `mvcc`'s
errors (from their facts), `rpctypes`' (from its), its metrics `streamFailures` (with its label
names) and the four
`watchSendLoop*` histograms (translated, over prometheus's `NewHistogram` and `ExponentialBuckets`
specs; until 2026-11-19 the trust-boundary axioms `<X>_init`),
`traceutil.Tracer`, and `progressReportIntervalMu`, initialized here, guarding
`progressReportInterval` (`10 * time.Minute`: `intervalP`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.crypto.tls.Init
public import Proof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.credentials.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.config.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.health.Init
public import Proof.google_golang_org.grpc.health.grpc_health_v1.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.status.Init
public import Proof.math.rand.Init
public import Proof.unicode.utf8.Init
public import Perennial.Proof.sync.RWMutexGuard

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
namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([sentBytes.init,
        receivedBytes.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `toGRPCErrorMap = map[error]error{...}` (`util.go`): a map whose values are `rpctypes.ErrGRPC*` errors (and `ErrTooManyRequests`, `ErrMemberNotEnoughStarted`), non-nil; mvcc's `ErrFutureRev` and `ErrCompacted` (the values of their cells) map to `ErrGRPCFutureRev` and `ErrGRPCCompacted`, and no other key maps to an error with one of those two descriptions, nor has one itself (k8s etcd3 7c: `grpcErrMapOk`), and the two have their `errors.New` descriptions (`kvstore.go:38-39`; k8s etcd3 7c-2 part 2, G2-a); every value is one grpc's `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6: the `status.Error`s and the two `EtcdError`s, leaves with only `Code` and `Error`); the value of each variable of `grpcErrKeyGlobals` (the literal's 53 keys) is a key (k8s etcd3 7c-2 part 2, S2: stated as a persistent wand on the variable's persisted cell, asserting no cell of another package). -/
axiom toGRPCErrorMap_init :
    {{ (True : IProp GF) }} (App (Val toGRPCErrorMap.init) (Val #()))
    {{ RET #(); ∃ (mp : Loc) (M : GMap GoInterface GoInterface) (kf kc : GoInterface), globalAddr toGRPCErrorMap ↦ mp ∗ mp ↦$□ M ∗ globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ kf ∗ globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ kc ∗ □ (∀ (k v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗ □ (∀ (g : GoString) (k : GoInterface), ⌜g ∈ grpcErrKeyGlobals⌝ → globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝) ∗ ⌜grpcErrMapOk M kf kc⌝ }}

/-- `clientRequests = prometheus.NewCounterVec(..., []string{"type", "client_api_version"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom clientRequests_init :
    {{ (True : IProp GF) }} (App (Val clientRequests.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr clientRequests ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"type", go!"client_api_version"]⌝ }}

/-- `streamFailures = prometheus.NewCounterVec(..., []string{"Type", "API"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom streamFailures_init :
    {{ (True : IProp GF) }} (App (Val streamFailures.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr streamFailures ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"Type", go!"API"]⌝ }}

end go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
end opaqueInits

end Perennial
