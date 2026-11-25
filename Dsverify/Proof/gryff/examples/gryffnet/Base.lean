/-
The package fact of `gryff.examples.gryffnet` (dsv-gryff, notes/dsv-gryff.md): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Proof.bufio.Init
public import Perennial.Proof.encoding.binary.Link
public import Proof.net.Init
public import Dsverify.Proof.net.rpc.Init
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.anishathalye.porcupine.Init
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Init
public import Dsverify.Proof.gryff.src.clientproto.Init
public import Dsverify.Proof.gryff.src.gryff.Init
public import Dsverify.Proof.gryff.src.gryffproto.Init
public import Dsverify.Proof.gryff.src.masterlib.Init
public import Dsverify.Proof.gryff.src.serverlib.Init
public import Dsverify.Proof.gryff.src.state.Init
public import Perennial.Proof.errors.Link
public import Dsverify.Proof.gryff.src.genericsmrproto.Init
public import Dsverify.Proof.gryff.src.masterproto.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.examples.gryffnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.examples.gryffnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.examples.gryffnet :=
  build_get_is_pkg_init_wf

end def_

end gryff.examples.gryffnet
end Perennial
