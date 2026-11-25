/-
The package fact of `github_com.imdea_software.swiftpaxos.master` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.master
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.net.http.Init
public import Dsverify.Proof.net.rpc.Init
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Init
public import Proof.net.Init
public import Proof.encoding.json.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.master

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.master :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.master :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.master
end Perennial
