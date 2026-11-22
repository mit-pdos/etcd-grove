/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Init
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

namespace github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights are its
initializer's resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s
precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.wal, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regKeys)]

end github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant

end Perennial
