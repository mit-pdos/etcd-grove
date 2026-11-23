/-
The package fact of `math.rand` (the gryff kit, notes/dsv-gryff.md, "Hypotheses"): `True` for now, in
the shape of dsv-vr's names-only packages (`Dsverify/Proof/encoding/json/Base.lean` there); its dependencies as generated (`define_is_pkg_init`, `build_get_is_pkg_init_wf`).
-/
module

public import Perennial.GeneratedProof.math.rand
public import Perennial.Proof.sync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace math.rand

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.rand :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.rand :=
  build_get_is_pkg_init_wf

end def_

end math.rand

end Perennial
