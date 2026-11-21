/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.membership`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`membershipInit`, `etcdserver/apply/Base.lean`): `ClusterVersionMetrics` holds a
fixed pointer (a `*prometheus.GaugeVec`, with its label names: D19l (iii)), and (D43 M4,
2026-10-26) every error variable its `errors.New` error (`errorsNewVars membershipErrMsgs`). Its
initializer allocates its error variables, initializes its imports, runs their translated
initializers (`errors.go`: `errors.New` calls, Perennial's `errors.wp_New_errorString`; translated
since 2026-11-19, until then the trust-boundary axiom `errorsNewVarsInit`) and its other variables'
initializers (translated 2026-11-19, until then untranslated, `opaqueInitsOk`: the gauge vector
`knownPeers`, the gauge `isLearner`, and the store paths `StoreMembersPrefix` and
`storeRemovedMembersPrefix`, `path.Join` calls, over its proof), and the one the fact reads, `ClusterVersionMetrics`
(`metrics.go`: `prometheus.NewGaugeVec(...)`, translated, over its spec; until 2026-11-19 the
trust-boundary axiom `ClusterVersionMetrics_init`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Proof.encoding.json.Init
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.notify.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.path.Init
public import Perennial.Proof.errors.NewVar
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

namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"cluster" go!"version",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"known_peers",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"is_learner"]

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names: their registration rights are its initializer's
resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`). -/
def regQs : List (GoString × List GoString) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regNames)]

/-- The metric names its initializer registers, with those of its import closure: its
`wp_initialize'`'s precondition has the rights to register them (`namesFree`). -/
def initNames : List GoString := regQs.flatMap (·.2)

end go_etcd_io.etcd.server.v3.etcdserver.api.membership

end Perennial
