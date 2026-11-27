/-
The package fact of `gryff.examples.gryffnet.cmd.orch` (dsv-gryff, notes/dsv-gryff.md): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.gryff.examples.gryffnet.cmd.orch
public import Dsverify.Proof.gryff.examples.gryffnet.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.examples.gryffnet.cmd.orch

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.examples.gryffnet.cmd.orch :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.examples.gryffnet.cmd.orch :=
  build_get_is_pkg_init_wf

end def_

end gryff.examples.gryffnet.cmd.orch
end Perennial
