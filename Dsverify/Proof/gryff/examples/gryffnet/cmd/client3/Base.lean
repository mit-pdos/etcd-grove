/-
The package fact of `gryff.examples.gryffnet.cmd.client3` (dsv-gryff, notes/dsv-gryff.md): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.gryff.examples.gryffnet.cmd.client3
public import Dsverify.Proof.gryff.examples.gryffnet.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.examples.gryffnet.cmd.client3

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.examples.gryffnet.cmd.client3 :=
  build_get_is_pkg_init_wf

end def_

end gryff.examples.gryffnet.cmd.client3
end Perennial
