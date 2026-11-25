/-
Package initialization of `k8s_io.client_go.tools.cache`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`k8sCacheInit`, `Proof/k8s_io/apiserver/pkg/storage/cacher/Base.lean`; phase 4
of the DaemonSet plan, 2026-10-27): `ErrFIFOClosed` and `errorStopRequested` (untranslated
`errors.New` calls, `fifo.go`, `reflector.go`) hold some error each, for good: the trust-boundary
axioms `ErrFIFOClosed_init` and `errorStopRequested_init`. Its initializer allocates its translated
variables (`informer_metrics.go`: `globalInformerMetricsProvider`, a
`noopInformerMetricsProvider{}`, and the zero `setInformerMetricsProviderOnce`;
`mutation_detector.go`: `mutationDetectionEnabled`, `false`), initializes its imports, runs the
other variables' untranslated initializers, which the trust-boundary axiom `opaqueInitsOk` says run
without panicking, and the translated ones, and its translated `init` (`mutation_detector.go:35`),
which stores in `mutationDetectionEnabled` whether `KUBE_CACHE_MUTATION_DETECTOR` parses as true
(`os.Getenv`: the trust-boundary axiom `os.Getenv.wp_proof`; `strconv.ParseBool.wp_proof`). (Until
2026-11-24 the `init`, translated but in chunks, was the trust-boundary axiom `initFuncsOk`, and
`mutationDetectionEnabled`'s initializer untranslated.)
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.math.rand.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.container.heap.Init
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.unstructured.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1beta1.Init
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.sharding.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
public import Proof.k8s_io.apimachinery.pkg.util.cache.Init
public import Proof.k8s_io.apimachinery.pkg.util.diff.Init
public import Proof.k8s_io.apimachinery.pkg.util.naming.Init
public import Proof.k8s_io.apimachinery.pkg.util.net.Init
public import Proof.k8s_io.apimachinery.pkg.util.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.util.sets.Init
public import Proof.k8s_io.apimachinery.pkg.util.wait.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.client_go.features.Init
public import Proof.k8s_io.client_go.rest.Init
public import Proof.k8s_io.client_go.tools.cache.synctrack.Init
public import Proof.k8s_io.client_go.tools.pager.Init
public import Proof.k8s_io.client_go.util.consistencydetector.Init
public import Proof.k8s_io.client_go.util.watchlist.Init
public import Proof.k8s_io.klog.v2.Init
public import Proof.k8s_io.utils.buffer.Init
public import Proof.k8s_io.utils.clock.Init
public import Proof.k8s_io.utils.ptr.Init
public import Proof.k8s_io.utils.trace.Init
public import Proof.os.Init

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
namespace k8s_io.client_go.tools.cache
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.client_go.tools.cache`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrZeroLengthDeltasObject.init,
        defaultMinWatchTimeout.init,
        defaultMaxWatchTimeout.init,
        defaultBackoffInit.init,
        defaultBackoffMax.init,
        defaultBackoffReset.init,
        defaultBackoffFactor.init,
        defaultBackoffJitter.init,
        internalPackages.init,
        unsupportedTableGVK.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `ErrFIFOClosed = errors.New("DeltaFIFO: manipulating with closed queue")` (`fifo.go`): an error. -/
axiom ErrFIFOClosed_init :
    {{ (True : IProp GF) }} (App (Val ErrFIFOClosed.init) (Val #()))
    {{ RET #(); ∃ e : GoInterface, globalAddr ErrFIFOClosed ↦ e }}

/-- `errorStopRequested = errors.New("stop requested")` (`reflector.go`): an error. -/
axiom errorStopRequested_init :
    {{ (True : IProp GF) }} (App (Val errorStopRequested.init) (Val #()))
    {{ RET #(); ∃ e : GoInterface, globalAddr errorStopRequested ↦ e }}

end k8s_io.client_go.tools.cache
end opaqueInits

end Perennial
