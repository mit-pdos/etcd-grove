/-
The package fact of `github_com.imdea_software.swiftpaxos_epaxos.epaxos` (dsv-epaxos, notes/dsv-epaxos.md): `True` (`errVarintOverflow`, `deferMap` (to be refined: the lab's `epaxosPkgStateDef`)).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.epaxos
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.rpc.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.state.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos_epaxos.epaxos

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos_epaxos.epaxos
end Perennial
