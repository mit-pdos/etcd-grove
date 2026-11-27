/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (`health.go`, 2026-11-26; until then untranslated, `opaqueInitsOk`): the
counters `healthSuccess` and `healthFailed` (over prometheus's `NewCounter` spec) and the vectors
`healthCheckGauge` and `healthCheckCounter` (`NewGaugeVec`, `NewCounterVec`); then its translated `init`
function (until then the trust-boundary axiom `initFuncsOk`), which registers the four with prometheus's
default registry (`MustRegister`), with the rights to their names.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.Base
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.github_com.prometheus.client_golang.prometheus.MetricLaws
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.runtime.PkgInitRes

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

namespace go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"health_success",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"health_failures",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"healthcheck",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"healthchecks_total"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.regKeys)]

end go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp

end Perennial
