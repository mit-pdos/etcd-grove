/-
The package fact of encoding/gob (names only, never reached): `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.encoding.gob
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace encoding.gob

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.gob :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.gob :=
  build_get_is_pkg_init_wf

end def_

end encoding.gob
end Perennial
