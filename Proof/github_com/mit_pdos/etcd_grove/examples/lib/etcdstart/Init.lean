/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.lib.etcdstart`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.server.v3.config.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.keepalive.Init
public import Proof.net.Init
public import Proof.net.http.Init

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
