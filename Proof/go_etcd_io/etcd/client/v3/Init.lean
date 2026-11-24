/-
Package initialization of `go_etcd_io.etcd.client.v3`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`clientv3Init`, `cache/v3/Base.lean`): `noPrefixEnd` (`op.go`, translated:
`[]byte{0}`) and `defaultOptions` (`retry_interceptor.go`, translated since 2026-11-22: `&options{...}`
whose backoff function, `backoffLinearWithJitter`'s, returns; until then the trust-boundary axiom
`defaultOptions_init`), and its translated
`valCtxCh`, `zeroTime` (`time.Unix(0, 0)`, `time.Unix.wp_proof`: proved over Perennial's translation since
2026-11-20, until then a trust-boundary axiom) and
`maxBackoff`, and `LeaseResponseChSize` (`lease.go`, translated: `16`; until 2026-11-19 the
trust-boundary axiom `LeaseResponseChSize_init`), and the translated constants
`defaultUnaryMaxRetries`, `defaultStreamMaxRetries` and `defaultBackoffWaitBetween`
(`options.go`). (prove-smallinits, 2026-11-20) Its other variables' initializers are translated
too: the three `errors.New` errors, the call options (grpc's `WaitForReady`, `MaxCallSendMsgSize`,
`MaxCallRecvMsgSize`), `defaultCallOpts` (their slice) and `defaultBackoffJitterFraction` (until then
`opaqueInitsOk` and the trust-boundary axioms `defaultCallOpts_init`,
`defaultBackoffJitterFraction_init`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.crypto.tls.Init
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.logutil.Init
public import Proof.go_etcd_io.etcd.client.v3.credentials.Init
public import Proof.go_etcd_io.etcd.client.v3.internal.endpoint.Init
public import Proof.go_etcd_io.etcd.client.v3.internal.resolver.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.google_golang_org.grpc.credentials.insecure.Init
public import Proof.google_golang_org.grpc.keepalive.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.peer.Init
public import Proof.google_golang_org.grpc.status.Init
public import Proof.math.rand.Init
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
namespace go_etcd_io.etcd.client.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.client.v3`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.client.v3
end opaqueInits

end Perennial
