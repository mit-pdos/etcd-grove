/-
The package fact of `gryff.src.genericsmr` (dsv-gryff, notes/dsv-gryff.md): `True`.
-/
module

public import Dsverify.GeneratedProof.gryff.src.genericsmr
public import Dsverify.Proof.bufio.Init
public import Perennial.Proof.encoding.binary.Link
public import Dsverify.Proof.gryff.src.fastrpc.Init
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.gryff.src.clientproto.Init
public import Dsverify.Proof.gryff.src.genericsmrproto.Init
public import Perennial.Proof.io.Link
public import Net.Proof.net.Init
public import Net.Proof.os.Init
public import Dsverify.Proof.gryff.src.state.Init
public import Perennial.Proof.time.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.log.Link
public import Dsverify.Proof.gryff.src.dlog.Init
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.gryff.src.stats.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.genericsmr

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.genericsmr :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.genericsmr :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.genericsmr
end Perennial
