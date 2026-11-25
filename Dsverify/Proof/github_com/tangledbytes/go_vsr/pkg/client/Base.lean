/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.client` (the vr kit, notes/dsv-vr.md): `True` for now (the fact a proof needs
is added with that proof).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.client
public import Perennial.Proof.io.Base
public import Dsverify.Proof.log.slog.Base
public import Perennial.Proof.sort.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.ipv4port.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.network.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.queue.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.client

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.client.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.client
end Perennial
