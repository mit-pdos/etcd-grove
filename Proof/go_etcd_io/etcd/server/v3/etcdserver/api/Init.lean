/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`capInit`, `CapPool.lean`; prove-ps2-cap, 2026-11-23, until then `True`):
`enableMapMu`'s guard and its reader slots, pooled at level 0, over `enabledMap` holding `nil` or a
read-only map. Its initializer initializes its imports, allocates its variables and runs the
translated initializer of `capabilityMaps` (a map literal of map literals) and its translated `init`
function, which sets `enabledMap` to a map literal (prove-smallinits, 2026-11-20; until then the
trust-boundary axioms `opaqueInitsOk` and `initFuncsOk`), and makes the fact from the map, made
read-only, and the fresh lock (`capInit_alloc`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
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

namespace go_etcd_io.etcd.server.v3.etcdserver.api

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regKeys)]

end go_etcd_io.etcd.server.v3.etcdserver.api

end Perennial
