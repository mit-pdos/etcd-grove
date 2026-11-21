/-
Package initialization instance of `github.com/jonboulle/clockwork` (the compactor's clock, names only), here rather than in the server's `BaseApply.lean`
(the spec-first pilot's freeze, 2026-10-27: so that the package's definitions do not import the
server's). An assumption about package initialization, `True` (no variable its proofs read).
-/
module

public import GeneratedProof.github_com.jonboulle.clockwork
public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace github_com.jonboulle.clockwork

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.jonboulle.clockwork :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.jonboulle.clockwork :=
  build_get_is_pkg_init_wf

end github_com.jonboulle.clockwork

end init

end Perennial
