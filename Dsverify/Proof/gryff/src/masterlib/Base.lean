/-
The package fact of `gryff.src.masterlib` (dsv-gryff, notes/dsv-gryff.md): `True`.
-/
module

public import Dsverify.GeneratedProof.gryff.src.masterlib
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.net.rpc.Init
public import Proof.net.Init
public import Dsverify.Proof.gryff.src.masterproto.Init
public import Dsverify.Proof.net.http.Init
public import Perennial.Proof.time.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.log.Link
public import Dsverify.Proof.gryff.src.genericsmrproto.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.masterlib

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.masterlib :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.masterlib :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.masterlib
end Perennial
