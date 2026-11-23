/-
The package fact of go-craq's `examples.craqnet.cmd.server5` (the craq kit, notes/dsv-craq.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.examples.craqnet.cmd.server5
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.examples.craqnet.cmd.server5

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
-- (net/rpc's and net/http's package facts: hypotheses, as in `examples/craqnet/Base.lean`)
variable [IsPkgInit (IProp GF) pkg_id.net.rpc] [GetIsPkgInitWf (IProp GF) pkg_id.net.rpc]
variable [IsPkgInit (IProp GF) pkg_id.net.http] [GetIsPkgInitWf (IProp GF) pkg_id.net.http]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server5 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server5 :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.examples.craqnet.cmd.server5
end Perennial
