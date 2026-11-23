/-
The package fact of io/ioutil (names only, never reached): `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.io.ioutil
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace io.ioutil

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io.ioutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io.ioutil :=
  build_get_is_pkg_init_wf

end def_

end io.ioutil
end Perennial
