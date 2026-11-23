/-
The package fact of `crypto.tls` for the part `Dsverify/`: `True` (the main tree's translation, names only; the main tree declares the same fact in etcd's packages). It has no proof that reads
its variables; the fact exists so that `net/http`'s and `net/rpc`'s initialization hypotheses
(`Dsverify/Proof/net/{http,rpc}/Init.lean`) can name every package their initializers reach.
-/
module

public import GeneratedProof.crypto.tls
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace crypto.tls

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.tls :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.tls :=
  build_get_is_pkg_init_wf

end def_

end crypto.tls
end Perennial
