/-
The package fact of `github_com.imdea_software.swiftpaxos.client` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True`: the node ghost `nodeGhost` is the boot thread's, unclaimed (`client.freshAt`; the lab's `client.pkgSt`). Its initializer is not generated: its first run hands the node's boot thread owned resources Perennial's `wp_initialize'` cannot return (notes/dsv-swiftpaxos.md, "Package initialization"); its proof is hand-written.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.client
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.github_com.google.uuid.Init
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.math.rand.Link
public import Dsverify.Proof.net.rpc.Init
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Init
public import Net.Proof.net.Init
public import Proof.encoding.json.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.client

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.client :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.client :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.client
end Perennial
