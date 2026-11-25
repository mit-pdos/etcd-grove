/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.ipv4port` (the vr kit, notes/dsv-vr.md): `True` for now (the fact a proof needs
is added with that proof).
-/
module

public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.ipv4port
public import Perennial.Proof.errors.Base
public import Perennial.Proof.fmt.Base
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.ipv4port

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.ipv4port.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.ipv4port
end Perennial
