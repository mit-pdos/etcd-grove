/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.txn`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`txnInit`, `Base.lean`): `lease.ErrLeaseNotFound` and `etcdserver/errors.ErrKeyNotFound`
(from their packages' facts) and its counter `slowApplies` (`metrics.go`, translated: `NewCounter`'s
spec; until 2026-11-19 the trust-boundary axiom `slowApplies_init`). Its histogram vectors `applySec` and
`rangeSec` are translated too (`NewHistogramVec`'s spec; prove-smallinits, 2026-11-20, until then
`opaqueInitsOk`), and in its fact with their label
names (prove-etcdserver, 2026-11-20: `metrics.go`'s observers, translated, read them).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
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

namespace go_etcd_io.etcd.server.v3.etcdserver.txn

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"apply_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"range_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"slow_apply_total"]

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names: their registration rights are its initializer's
resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`). -/
def regQs : List (GoString × List GoString) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regNames), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames), (pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regNames)]

/-- The metric names its initializer registers, with those of its import closure: its
`wp_initialize'`'s precondition has the rights to register them (`namesFree`). -/
def initNames : List GoString := regQs.flatMap (·.2)

end go_etcd_io.etcd.server.v3.etcdserver.txn

end Perennial
