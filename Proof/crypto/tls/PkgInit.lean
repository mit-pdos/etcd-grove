/-
The package fact of `crypto/tls` (names only: the types `transport.TLSInfo`'s fields and
`clientv3.Config.TLS` name): `True`. It has no proof that reads its variables. Shared by every tree that
imports the package (L1, 2026-11-24: until then declared in `cache/v3/Base.lean` and in the server's
`apply/Base.lean`, and again in `Dsverify/`, for `net/http`'s and `net/rpc`'s initialization
hypotheses, which name every package their initializers reach).
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
