/-
Package initialization of `k8s_io.apiserver.pkg.storage`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`storageInit`, `storage/etcd3/Base.lean`): `RequestWatchProgress` and
`tooLargeResourceVersionCauseMsg` hold strings, and `Everything` holds, for good, a predicate with no
shard selector whose label and field selectors' `Empty()` is `true` (`everythingOk`, from the two
specs' posts; k8s 7f-5b H2).
Its initializer allocates its translated variables (`errors.go`, `feature.go`, `selection_predicate.go`:
six `errors.New` errors, the map `errCodeToMessage`, three strings, and `Everything`, a
`SelectionPredicate` of `labels.Everything()` and `fields.Everything()`, both proved:
`labels.Everything.wp_proof` (#25, 2026-11-21), `fields.Everything.wp_proof`), initializes
its imports and runs the translated initializers.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.base64.Init
public import Proof.encoding.json.Init
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.k8s_io.apimachinery.pkg.api.validate.content.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.sharding.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
public import Proof.k8s_io.apimachinery.pkg.util.validation.field.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.apiserver.pkg.features.Init
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
public import Proof.path.Init
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

end Perennial
