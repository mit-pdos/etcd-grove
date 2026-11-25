/-
The package fact of `github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3` (dsv-epaxos, notes/dsv-epaxos.md): `True` (no variables a proof reads).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3 :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3
end Perennial
