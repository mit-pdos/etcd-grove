/-
The package-initialization instance of semver: fact `True` (names only: `MustParse`, `Version.LessThan`/`String`). One home, shared by the server's
`Base.lean` files and the WAL (until 2026-11-15 declared in the lease's `Base.lean` and the WAL's `DepsPkgInit.lean`; notes/wal-lean-integration.md).
-/
module

public import GeneratedProof.github_com.Masterminds.semver.v3
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace github_com.Masterminds.semver.v3

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  build_get_is_pkg_init_wf

end github_com.Masterminds.semver.v3

end init

end Perennial
