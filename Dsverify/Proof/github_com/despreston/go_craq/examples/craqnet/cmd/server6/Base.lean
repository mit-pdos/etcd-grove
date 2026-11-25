/-
The package fact of go-craq's `examples.craqnet.cmd.server6` (the craq kit, notes/dsv-craq.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.examples.craqnet.cmd.server6
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Base
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server6

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server6 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server6 :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.examples.craqnet.cmd.server6
end Perennial
