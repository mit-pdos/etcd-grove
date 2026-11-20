/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.v3election`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`v3electionInit`, `etcdserver/api/v3election/Base.lean`; the auth plan's A3c,
2026-10-24): `ErrMissingLeaderKey` holds a fixed non-nil error. Its initializer allocates it,
initializes its imports and runs its translated initializer (an `errors.New` call, `election.go`;
Perennial's `context.wp_New_errorString`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.concurrency.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.v3electionpb.Init
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
