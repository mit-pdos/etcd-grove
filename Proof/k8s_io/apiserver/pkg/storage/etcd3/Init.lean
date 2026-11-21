/-
Package initialization of `k8s_io.apiserver.pkg.storage.etcd3`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`EtcdGrove.k8s.registryFact`, `RegistryDefs.lean`): `endpointsMapMu` is a mutex over
the compactor registry, at the registry's name (`CompactorRegistry`, a variable of every package
importing this one). Its initializer allocates its variables, initializes its imports, runs
the translated initializers (`errTooMany`, an `errors.New` error; `typeToMessage`, a map literal;
`defaultWatcherMaxLimit`, kept read-only in the fact) and its translated `init` functions: `compact.go`'s makes
`endpointsMap` (then the registry's mutex is made, with the map empty), `logger.go`'s sets grpc's logger (`grpclog.SetLoggerV2`, names-only: the
trust-boundary axiom `grpclog.SetLoggerV2.wp_proof`), `watcher.go`'s stores in
`fatalOnDecodeError` whether `KUBE_PANIC_WATCH_DECODE_ERROR` parses as true (`os.Getenv` and
`strconv.ParseBool`: the trust-boundary axiom `os.Getenv.wp_proof`, and `strconv.ParseBool.wp_proof`, proved
over Perennial's translation since 2026-11-20).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.iter.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.json.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.grpclog.Init
public import Proof.google_golang_org.grpc.status.Init
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.unstructured.Init
public import Proof.k8s_io.apimachinery.pkg.conversion.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.util.errors.Init
public import Proof.k8s_io.apimachinery.pkg.util.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.util.wait.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.apiserver.pkg.audit.Init
public import Proof.k8s_io.apiserver.pkg.endpoints.request.Init
public import Proof.k8s_io.apiserver.pkg.features.Init
public import Proof.k8s_io.apiserver.pkg.storage.Init
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.metrics.Init
public import Proof.k8s_io.apiserver.pkg.storage.feature.Init
public import Proof.k8s_io.apiserver.pkg.storage.value.Init
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
public import Proof.k8s_io.apiserver.pkg.util.flowcontrol.Init
public import Proof.k8s_io.component_base.tracing.Init
public import Proof.k8s_io.klog.v2.Init
public import Proof.k8s_io.utils.clock.Init
public import Proof.net.http.Init
public import Proof.os.Init
public import Proof.path.Init
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.sync.atomic.Link

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

section toLoggerV2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- A `klogWrapper` is not grpc's `*componentData` (`SetLoggerV2`'s premise). -/
theorem k8s_io.apiserver.pkg.storage.etcd3.klogWrapper_ne_componentData (v w : val) :
    interface.mkOk k8s_io.apiserver.pkg.storage.etcd3.klogWrapper.ty v ≠
      interface.mkOk (go.GoType.PointerType google_golang_org.grpc.grpclog.componentData.ty) w := by
  intro h
  injection h with h
  injection h with h
  unfold k8s_io.apiserver.pkg.storage.etcd3.klogWrapper.ty at h
  cases h

end toLoggerV2

end Perennial
