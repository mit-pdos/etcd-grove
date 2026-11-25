/-
The package fact of `github_com.imdea_software.swiftpaxos_epaxos.config` (dsv-epaxos, notes/dsv-epaxos.md): `True` (no variables a proof reads).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.config
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Proof.bufio.Init
public import Proof.os.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos_epaxos.config

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.config :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.config :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos_epaxos.config
end Perennial
