/-
The package fact of `github_com.rs.zerolog`: `True` (names only here (no model: notes/dsv-rabia.md), no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.rs.zerolog
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.rs.zerolog

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.rs.zerolog :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.rs.zerolog :=
  build_get_is_pkg_init_wf

end def_

end github_com.rs.zerolog
end Perennial
