/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.version`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`membership/PkgInit.lean`; grpcerrmap, 2026-11-26, `True` until then): every error
variable its `errors.New` error (`errorsNewVars versionErrMsgs`), keys of `v3rpc`'s error map. Its
initializer initializes its imports, allocates its variables and runs their translated initializers
(`errors.go`: `errors.New` calls; until 2026-11-19 untranslated, `opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.PkgInit
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_uber_org.zap.Init
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
