/-
The package fact of `gryff.src.dlog` (dsv-gryff, notes/dsv-gryff.md): `True` (`DLOG`, `false`, is read only to decide whether to print).
-/
module

public import Dsverify.GeneratedProof.gryff.src.dlog
public import Perennial.Proof.log.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.dlog

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.dlog :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.dlog :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.dlog
end Perennial
