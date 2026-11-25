/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.queue` (the vr kit, notes/dsv-vr.md): `True` for now (the fact a proof needs
is added with that proof).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.queue
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.queue

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.queue.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.queue :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.queue :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.queue
end Perennial
