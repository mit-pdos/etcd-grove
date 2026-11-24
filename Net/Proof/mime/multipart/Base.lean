/-
The package fact of `mime.multipart` (the part `Net/`'s translation): `True`. No proof reads its variables;
the fact exists so that the initialization facts of `net/http` and `net/rpc`
(`Net/Proof/net/{http,rpc}/PkgInit.lean`) can name every package their initializers reach.
Shared by `Net/` and `Dsverify/` (rpc-driver, 2026-11-24: until then `Dsverify/Proof/mime/multipart/Base.lean`).
-/
module

public import Net.GeneratedProof.mime.multipart
public import Net.Proof.net.textproto.Base
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
