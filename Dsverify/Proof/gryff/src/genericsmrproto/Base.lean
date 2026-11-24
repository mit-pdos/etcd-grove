/-
The package fact of `gryff.src.genericsmrproto` (dsv-gryff, notes/dsv-gryff.md): `True`.
-/
module

public import Dsverify.GeneratedProof.gryff.src.genericsmrproto
public import Dsverify.Proof.gryff.src.state.Init
public import Dsverify.Proof.gryff.src.fastrpc.Init
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.genericsmrproto

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.genericsmrproto :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.genericsmrproto :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.genericsmrproto
end Perennial
