/-
The package fact of `mime.multipart` for the part `Dsverify/`: `True` (the part `Net/`'s translation, from models-rpc-http). It has no proof that reads
its variables; the fact exists so that `net/http`'s and `net/rpc`'s initialization hypotheses
(`Dsverify/Proof/net/{http,rpc}/Init.lean`) can name every package their initializers reach.
-/
module

public import Net.GeneratedProof.mime.multipart
public import Dsverify.Proof.net.textproto.Base
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace mime.multipart

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.mime.multipart :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.mime.multipart :=
  build_get_is_pkg_init_wf

end def_

end mime.multipart
end Perennial
