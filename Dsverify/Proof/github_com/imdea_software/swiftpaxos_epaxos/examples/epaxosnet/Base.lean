/-
The package fact of `github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet` (dsv-epaxos, notes/dsv-epaxos.md): `True` (no variables a proof reads).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.math.rand.Base
public import Proof.bufio.Init
public import Proof.github_com.anishathalye.porcupine.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.state.Init
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Init
public import Proof.net.Init
public import Net.Proof.net.http.PkgInit
public import Net.Proof.net.rpc.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
