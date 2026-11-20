/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.etcd.wal`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.PkgInit
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.strings.Link
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.os.Init
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

namespace github_com.mit_pdos.etcd_grove.examples.etcd.wal

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names: their registration rights are its initializer's
resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`). -/
def regQs : List (GoString × List GoString) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.storage.wal, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regNames)]

/-- The metric names its initializer registers, with those of its import closure: its
`wp_initialize'`'s precondition has the rights to register them (`namesFree`). -/
def initNames : List GoString := regQs.flatMap (·.2)

end github_com.mit_pdos.etcd_grove.examples.etcd.wal

end Perennial
