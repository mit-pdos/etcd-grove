/-
The package fact of `net/rpc` (the part `Net/`'s model of it, `models/net/rpc`), as the shared
rpc-over-HTTP design (L2) states it: `DefaultServer` holds a server (`∃ γ, defaultServerAny γ`,
in any registry mode), the variables the server and the client read (`srvEnv`: `cliEnv`, with
`errFrame`, `ErrShutdown`, `io`'s errors, ...), `connected`'s answer line (`connectedStatus`, which
`DialHTTPPath` and `ServeHTTP` compare and write), and the codec registry's mutex (`codecMu`,
`codecInv`). All persistent. The exclusive state the initializer makes (the registry `codec` at
`nil`, `codecUnset`; `DefaultServer`'s registry, empty, `svcOwn`) is not a fact: net/rpc's first
initialization returns it (`InitFirst.lean`). Its well-formedness instance names the facts of every
package its initializer reaches, `net/http`'s closure included (`net/http/PkgInit.lean`). Used by
`Net/`'s initializers (`Init.lean`, `InitFirst.lean`, interim axioms). `Dsverify/` has its own
`True` fact (`Dsverify/Proof/net/rpc/Init.lean`): the two are never imported together (rpc-driver,
2026-11-24).
-/
module

public import Net.GeneratedProof.net.rpc
public import Net.Proof.net.rpc.ServerDefs
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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- The package's fact (see the file header). -/
def rpcInit : IProp GF :=
  iprop((∃ γ : GName, defaultServerAny γ) ∗ srvEnv ∗
    globalAddr net.rpc.connected ↦□ connectedStatus ∗
    sync.isMutex (globalAddr net.rpc.codecMu) (codecInv (GF := GF)))

instance rpcInit_persistent : Persistent (rpcInit (GF := GF)) := by
  unfold rpcInit; infer_instance

/-- The package's fact: `rpcInit`, with its imports' facts (`define_is_pkg_init`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.rpc :=
  define_is_pkg_init iprop(rpcInit)
/-- Its well-formedness: `get_is_pkg_init` gives its fact and, recursively, the facts of every
package its initializer reaches (its `PkgInfo` imports, which are the packages whose initializers
`initialize'` runs: `build_get_is_pkg_init_wf`). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  build_get_is_pkg_init_wf

end def_

end net.rpc
end Perennial
