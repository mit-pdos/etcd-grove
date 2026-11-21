/-
`net/http`'s package instance (prove-http3, 2026-11-21; until then in the server's
`apply/Base.lean`, which imports this file). Its fact is `True`: net/http is translated names-only
but for its constants, `StatusText` and `Header.Set`/`Get`, and its one translated import is
`net/textproto` (`Proof/net/textproto/Base.lean`), whose fact `isPkgInit pkg_id.net.http` carries.
-/
module

public import GeneratedProof.net.http
public import Proof.net.textproto.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace net.http

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

end net.http

end init

end Perennial
