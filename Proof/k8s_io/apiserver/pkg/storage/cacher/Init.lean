/-
Package initialization of `k8s_io.apiserver.pkg.storage.cacher`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.iter.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.conversion.Init
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
public import Proof.k8s_io.apimachinery.pkg.util.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.util.wait.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.apiserver.pkg.audit.Init
public import Proof.k8s_io.apiserver.pkg.endpoints.request.Init
public import Proof.k8s_io.apiserver.pkg.features.Init
public import Proof.k8s_io.apiserver.pkg.storage.Init
public import Proof.k8s_io.apiserver.pkg.storage.cacher.consistency.Init
public import Proof.k8s_io.apiserver.pkg.storage.cacher.delegator.Init
public import Proof.k8s_io.apiserver.pkg.storage.cacher.key.Init
public import Proof.k8s_io.apiserver.pkg.storage.cacher.progress.Init
public import Proof.k8s_io.apiserver.pkg.storage.cacher.store.Init
public import Proof.k8s_io.apiserver.pkg.storage.feature.Init
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
public import Proof.k8s_io.apiserver.pkg.util.flowcontrol.Init
public import Proof.k8s_io.client_go.tools.cache.Init
public import Proof.k8s_io.client_go.util.consistencydetector.Init
public import Proof.k8s_io.client_go.util.watchlist.Init
public import Proof.k8s_io.component_base.tracing.Init
public import Proof.k8s_io.klog.v2.Init
public import Proof.k8s_io.utils.clock.Init
public import Proof.net.http.Init

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

end Perennial
