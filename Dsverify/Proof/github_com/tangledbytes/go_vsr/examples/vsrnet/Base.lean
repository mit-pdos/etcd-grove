/-
The package fact of `github_com.tangledbytes.go_vsr.examples.vsrnet` (the vr kit, notes/dsv-vr.md): `True` for now (the fact a proof needs
is added with that proof).
-/
module

public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.examples.vsrnet
public import Perennial.Proof.io.Base
public import Dsverify.Proof.log.slog.Base
public import Net.Proof.net.Base
public import Perennial.Proof.time.Base
public import Proof.github_com.anishathalye.porcupine.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrkv.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.client.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.network.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.replica.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
