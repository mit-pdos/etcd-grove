/-
The package fact of `net.http.internal.ascii` for the part `Dsverify/`: `True` (the part `Net/`'s translation, from models-rpc-http). It has no proof that reads
its variables; the fact exists so that `net/http`'s and `net/rpc`'s initialization hypotheses
(`Dsverify/Proof/net/{http,rpc}/Init.lean`) can name every package their initializers reach.
-/
module

public import Net.GeneratedProof.net.http.internal.ascii
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http.internal.ascii

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http.internal.ascii :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http.internal.ascii :=
  build_get_is_pkg_init_wf

end def_

end net.http.internal.ascii
end Perennial
