/-
The package fact of `github_com.imdea_software.swiftpaxos.examples.swiftnet` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True` (no variables a proof reads). Its initializer is not generated: its first run hands the node's boot thread owned resources Perennial's `wp_initialize'` cannot return (notes/dsv-swiftpaxos.md, "Package initialization"); its proof is hand-written.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.examples.swiftnet
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.math.rand.Link
public import Net.Proof.net.http.PkgInit
public import Net.Proof.net.rpc.PkgInit
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.anishathalye.porcupine.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Init
public import Proof.net.Init
public import Proof.encoding.json.Base
public import Dsverify.Proof.os.signal.Init
public import Dsverify.Proof.encoding.gob.Init
public import Dsverify.Proof.github_com.google.uuid.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
