/-
The package fact of `net.rpc` (the net/rpc model, `models/net/rpc`), for the craq kit (notes/dsv-craq.md,
hypothesis H1): its variables the client reads, as its initialization leaves them (the content of `Net/`'s `net.rpc.cliEnv`): `io`'s errors, `poll.ErrDeadlineExceeded`, `errFrame` and `ErrShutdown` (`errors.New`'s), `debugLog` (`false`). `Net/` has no package fact for the model yet (plan phase 5.2, item 5); its
initialization is the hypothesis `Init.lean`'s `InitHyp`.
-/
module

public import Net.GeneratedProof.net.rpc
public import Perennial.Proof.errors.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.log.Base
public import Perennial.Proof.strings.Base
public import Dsverify.Proof.net.http.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

section deps
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `go.token`'s fact (names-only here): `True`. -/
instance dep_token_inst : IsPkgInit (IProp GF) pkg_id.go.token := define_is_pkg_init iprop(True)
instance dep_token_wf : GetIsPkgInitWf (IProp GF) pkg_id.go.token := build_get_is_pkg_init_wf

end deps

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : net.rpc.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.rpc :=
  define_is_pkg_init iprop(∃ eof ueof ed : GoInterface, isPkgInit (PROP := IProp GF) pkg_id.io ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
    errors.newVar net.rpc.errFrame go!"rpc: malformed frame" ∗
    errors.newVar net.rpc.ErrShutdown go!"connection is shut down" ∗
    globalAddr net.rpc.debugLog ↦□ false)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  build_get_is_pkg_init_wf

end def_

end net.rpc
end Perennial
