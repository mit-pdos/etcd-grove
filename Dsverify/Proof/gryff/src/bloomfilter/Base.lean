/-
The package fact of `gryff.src.bloomfilter` (dsv-gryff, notes/dsv-gryff.md): `True`.
-/
module

public import Dsverify.GeneratedProof.gryff.src.bloomfilter
public import Dsverify.Proof.gryff.src.bitvec.Init
public import Perennial.Proof.math.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.bloomfilter

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.bloomfilter :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.bloomfilter :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.bloomfilter
end Perennial
