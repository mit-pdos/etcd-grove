/-
The package fact of the counter instance's command `cmd/server` (`True`: no variables).
-/
module

public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server
end Perennial
