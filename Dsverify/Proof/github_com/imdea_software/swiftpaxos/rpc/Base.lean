/-
The package fact of `github_com.imdea_software.swiftpaxos.rpc` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.rpc
public import Perennial.Proof.io.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.rpc

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.rpc :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.rpc :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.rpc
end Perennial
