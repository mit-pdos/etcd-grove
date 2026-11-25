/-
The package fact of `gryff.src.masterlib` (dsv-gryff, notes/dsv-gryff.md): `True`.
-/
module

public import Dsverify.GeneratedProof.gryff.src.masterlib
public import Perennial.Proof.sync.Link
public import Net.Proof.net.rpc.PkgInit
public import Proof.net.Init
public import Dsverify.Proof.gryff.src.masterproto.Init
public import Net.Proof.net.http.PkgInit
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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.masterlib :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.masterlib :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.masterlib
end Perennial
