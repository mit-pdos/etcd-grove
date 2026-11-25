/-
The package fact of go-craq's `examples.craqnet.cmd.server1` (the craq kit, notes/dsv-craq.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.examples.craqnet.cmd.server1
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Base
public import Net.Proof.net.rpc.PkgInit
public import Net.Proof.net.http.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server1

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server1 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server1 :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.examples.craqnet.cmd.server1
end Perennial
