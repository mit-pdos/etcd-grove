/-
The package fact of `github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True` (a program: no variables). Its initializer is not generated: its first run hands the node's boot thread owned resources Perennial's `wp_initialize'` cannot return (notes/dsv-swiftpaxos.md, "Package initialization"); its proof is hand-written.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Proof.encoding.json.Base
public import Net.Proof.net.rpc.PkgInit
public import Net.Proof.net.http.PkgInit
public import Dsverify.Proof.os.signal.Init
public import Perennial.Proof.math.rand.Link
public import Dsverify.Proof.encoding.gob.Init
public import Dsverify.Proof.github_com.google.uuid.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0 :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0
end Perennial
