/-
The package fact of `rabia.examples.rabianet.cmd.client3`: `True` (no package-level state yet (notes/dsv-rabia.md: the lab's facts are to be ported)).
-/
module

public import Dsverify.GeneratedProof.rabia.examples.rabianet.cmd.client3
public import Net.Proof.net.Base
public import Dsverify.Proof.rabia.examples.rabianet.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace rabia.examples.rabianet.cmd.client3

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.examples.rabianet.cmd.client3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.examples.rabianet.cmd.client3 :=
  build_get_is_pkg_init_wf

end def_

end rabia.examples.rabianet.cmd.client3
end Perennial
