/-
Package initialization of `go_etcd_io.etcd.server.v3.lease`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`leaseInit`, `Base.lean`): the error variables `ErrNotPrimary`,
`ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge` (translated `errors.New` calls: leaf pointer errors
without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose `Error()` returns), `forever` (the zero
`time.Time`), the counters `leaseGranted`, `leaseRevoked`, `leaseRenewed` and the histogram `leaseTotalTTLs`
(`metrics.go`, translated: over prometheus's constructor specs; until 2026-11-19 the trust-boundary
axioms `<X>_init`). Its other variables' initializers are translated too (2026-11-19, until then
`opaqueInitsOk`): the rate and interval constants (`lessor.go`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.math.Link
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

namespace go_etcd_io.etcd.server.v3.lease

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"lease" go!"granted_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"lease" go!"revoked_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"lease" go!"renewed_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"lease" go!"ttl_total"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights are its
initializer's resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s
precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys)]

end go_etcd_io.etcd.server.v3.lease

end Perennial
