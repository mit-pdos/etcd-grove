/-
The package fact of `gryff.src.gryffcommon` (dsv-gryff, notes/dsv-gryff.md): `True`.
-/
module

public import Dsverify.GeneratedProof.gryff.src.gryffcommon
public import Dsverify.Proof.gryff.src.gryffproto.Init
public import Perennial.Proof.sort.Link
public import Dsverify.Proof.gryff.src.stats.Init
public import Dsverify.Proof.gryff.src.state.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.gryffcommon

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.gryffcommon :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.gryffcommon :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.gryffcommon
end Perennial
