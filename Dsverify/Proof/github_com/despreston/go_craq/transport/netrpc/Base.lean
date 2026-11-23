/-
The package fact of go-craq's `transport.netrpc` (the craq kit, notes/dsv-craq.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.transport.netrpc
public import Dsverify.Proof.github_com.despreston.go_craq.transport.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.transport.netrpc

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
-- net/rpc's package fact: a hypothesis until the model's initialization is proved (plan phase
-- 5.2, item 5; notes/dsv-craq.md, "Hypotheses")
variable [IsPkgInit (IProp GF) pkg_id.net.rpc] [GetIsPkgInitWf (IProp GF) pkg_id.net.rpc]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.transport.netrpc
end Perennial
