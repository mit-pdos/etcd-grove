/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.schema`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`schemaInit`, `etcdserver/Base.lean`): the `Meta`, `Key`, `Auth`, `AuthUsers` and
`AuthRoles` buckets, as `bucket.go` makes them, the consistent index's two key names (`cindex.go`),
the auth bucket's two key names and the auth backend's `authEnabled`/`authDisabled` values
(`auth.go`; the auth plan's S1, 2026-10-23), the lessor's `Lease` bucket (leases T3,
2026-10-25), the membership's `Members`, `MembersRemoved` and `Cluster` buckets (prove-ps2-members,
2026-11-22) and the alarm store's `Alarm` bucket (prove-ps2-v3alarm, 2026-11-24). Its initializer allocates and sets those translated variables (with the buckets'
names), initializes its imports and runs its other variables' initializers, all translated
(prove-initleft, 2026-11-21: `schemaChanges`, a map literal keyed by `version`'s versions, and the
interface assertions; until then the trust-boundary axiom `opaqueInitsOk`), and its `init` function
(`bucket.go`), whose trusted model does nothing (`TrustedCode/go_etcd_io/etcd/server/v3/storage/schema.lean`,
etcd-grove#32; until 2026-11-23 the trust-boundary axiom `initFuncsOk` said it returns).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.encoding.binary.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.leasepb.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.github_com.Masterminds.semver.v3.MapKey
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

namespace go_etcd_io.etcd.server.v3.storage.schema

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names: their registration rights are its initializer's
resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`). -/
def regQs : List (GoString × List GoString) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames)]

/-- The metric names its initializer registers, with those of its import closure: its
`wp_initialize'`'s precondition has the rights to register them (`namesFree`). -/
def initNames : List GoString := regQs.flatMap (·.2)

end go_etcd_io.etcd.server.v3.storage.schema

end Perennial
