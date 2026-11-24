/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.mvccfull`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
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

namespace github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regKeys)]

end github_com.mit_pdos.etcd_grove.examples.mvccfull

end Perennial
