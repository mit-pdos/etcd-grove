/-
The package fact of `net/rpc` (the part `Net/`'s model of it, `models/net/rpc`): `True`: the proofs of
its functions take what they read of its variables (`errFrame`, the codec registry) as their
preconditions (`ServerGhost.lean`, `Codec.lean`), not from the fact. Its well-formedness instance names
the facts of every package its initializer reaches, `net/http`'s closure included
(`net/http/PkgInit.lean`). Shared by `Net/` (its interim `wp_initialize'`, `Init.lean`) and
`Dsverify/` (its hypothesis `InitHyp`, `Dsverify/Proof/net/rpc/Init.lean`) (rpc-driver,
2026-11-24: until then declared in `Dsverify/Proof/net/rpc/Init.lean`).
-/
module

public import Net.GeneratedProof.net.rpc
public import Net.Proof.net.http.PkgInit
public import Net.Proof.go.token.Base
public import Perennial.Proof.log.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact: `True`, with its imports' facts (`define_is_pkg_init`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.rpc :=
  define_is_pkg_init iprop(True)
/-- Its well-formedness: `get_is_pkg_init` gives its fact and, recursively, the facts of every
package its initializer reaches (its `PkgInfo` imports, which are the packages whose initializers
`initialize'` runs: `build_get_is_pkg_init_wf`). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  build_get_is_pkg_init_wf

end def_

end net.rpc
end Perennial
