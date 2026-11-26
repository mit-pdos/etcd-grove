/-
Shared definitions of the proof of `examples/net/httpdriver/cmd/client`: the package fact of the driver's
`client` command (`True`: no variables).
-/
module

public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client
end Perennial
