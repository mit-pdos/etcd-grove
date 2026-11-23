/-
The package fact of the paxos kit (`examples/paxosnet`): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.xiang90.paxos.examples.paxosnet
public import Dsverify.Proof.github_com.xiang90.paxos.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.xiang90.paxos.examples.paxosnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.xiang90.paxos.examples.paxosnet :=
  build_get_is_pkg_init_wf

end def_

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
