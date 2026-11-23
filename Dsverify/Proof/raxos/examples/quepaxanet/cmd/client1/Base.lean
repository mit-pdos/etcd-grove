/-
The package fact of the QuePaxa kit's command `client1`: `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.raxos.examples.quepaxanet.cmd.client1
public import Net.Proof.net.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace raxos.examples.quepaxanet.cmd.client1

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client1 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.raxos.examples.quepaxanet.cmd.client1 :=
  build_get_is_pkg_init_wf

end def_

end raxos.examples.quepaxanet.cmd.client1
end Perennial
