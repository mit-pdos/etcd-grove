/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.assert` (the vr kit, notes/dsv-vr.md): `True` for now (the fact a proof needs
is added with that proof).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.assert
public import Perennial.Proof.fmt.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.assert

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.assert.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.assert :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.assert :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.assert
end Perennial
