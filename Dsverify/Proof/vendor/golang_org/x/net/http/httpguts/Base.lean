/-
The package fact of `vendor.golang_org.x.net.http.httpguts` for the part `Dsverify/`: `True` (the part `Net/`'s translation, names only). It has no proof that reads
its variables; the fact exists so that `net/http`'s and `net/rpc`'s initialization hypotheses
(`Dsverify/Proof/net/{http,rpc}/Init.lean`) can name every package their initializers reach.
-/
module

public import Net.GeneratedProof.vendor.golang_org.x.net.http.httpguts
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace vendor.golang_org.x.net.http.httpguts

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts :=
  build_get_is_pkg_init_wf

end def_

end vendor.golang_org.x.net.http.httpguts
end Perennial
