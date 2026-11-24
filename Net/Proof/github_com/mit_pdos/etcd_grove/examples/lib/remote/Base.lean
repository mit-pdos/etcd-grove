/-
Shared definitions of the proofs of `examples/lib/remote`: its package fact (`True`: no variables).
-/
module

public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.remote
public import Net.Proof.net.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
