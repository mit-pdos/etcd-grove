/-
Package initialization of `go_etcd_io.etcd.api.v3.version`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`api/v3/version/PkgInit.lean`): `Version` holds `"3.8.0-alpha.0"`, `V3_6`, `V3_7` and `V3_8`
fixed values and `MinClusterVersion` `"3.0.0"`. Its initializer allocates and sets its translated string
variables (`version.go`: `MinClusterVersion`, `Version`, `APIVersion`, `GitSHA`; translated since
2026-11-19, until then the trust-boundary axioms `Version_init` and `MinClusterVersion_init`), its `semver`
versions (`V3_0 = *semver.New(3, 0, 0, "", "")`, ...: `semver.New`'s spec, proved over the real code) and
`AllVersions` (a slice literal of them; prove-initleft, 2026-11-21: until then the trust-boundary axioms
`V3_6_init` and `opaqueInitsOk`), and runs its translated `init` function (prove-ps2-initfuncs,
2026-11-22; until then the trust-boundary axiom `initFuncsOk`): `APIVersion` set to
`fmt.Sprintf("%d.%d", ver.Major(), ver.Minor())` of `semver.NewVersion(Version)` when that parses
(`NewVersion`'s spec, the trust boundary; `Major`/`Minor` proved), left as it was otherwise.
-/
module

public import Proof.go_etcd_io.etcd.api.v3.version.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strings.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Perennial.Proof.bytes.Link

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
