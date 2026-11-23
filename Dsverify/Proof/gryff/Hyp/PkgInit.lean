/-
**Hypothesis (notes/dsv-gryff.md, "Hypotheses"):** the post-initialization state of the net/rpc and
net/http models (`Net/Code/net/{rpc,http}.lean`), which `Net/` does not define yet (plan 5.2 item 5:
net/rpc's package initialization over net/http's initializers), and of `math/rand`, which Perennial
translates but gives no `IsPkgInit` instance (the lab's `Harness/Proof/math/rand.lean`). Kept abstract: a class `LibPkgState`
whose fields are the two packages' `isPkgInit` bodies, from which their `IsPkgInit` instances are
built. Everything proved here holds for any choice; the hypothesized specs of the two packages'
functions (`Hyp/NetRpc.lean`, `Hyp/NetHttp.lean`) take these as their package preconditions. When
`Net/` defines them, this module goes and their instances are imported instead.
-/
module

public import Net.GeneratedProof.net.rpc
public import Net.GeneratedProof.net.http
public import Perennial.GeneratedProof.math.rand
public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.hyp

/-- The (hypothesized) package states of the net/rpc and net/http models: their `IsPkgInit`
instances (post-initialization predicates) and the well-formedness of `get_is_pkg_init` for them
(their import closures reach packages with no instance here: `go/token`, `net/url`, `crypto/tls`,
`net/textproto`, ...). -/
class LibPkgState (GF : BundledGFunctors) where
  netRpcInit : IsPkgInit (IProp GF) pkg_id.net.rpc
  netRpcWf : GetIsPkgInitWf (IProp GF) pkg_id.net.rpc
  netHttpInit : IsPkgInit (IProp GF) pkg_id.net.http
  netHttpWf : GetIsPkgInitWf (IProp GF) pkg_id.net.http
  mathRandInit : IsPkgInit (IProp GF) pkg_id.math.rand
  mathRandWf : GetIsPkgInitWf (IProp GF) pkg_id.math.rand

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

instance netRpc_isPkgInit_inst [s : LibPkgState GF] : IsPkgInit (IProp GF) pkg_id.net.rpc :=
  s.netRpcInit
instance netRpc_get_isPkgInit_wf_inst [s : LibPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  s.netRpcWf
instance netHttp_isPkgInit_inst [s : LibPkgState GF] : IsPkgInit (IProp GF) pkg_id.net.http :=
  s.netHttpInit
instance netHttp_get_isPkgInit_wf_inst [s : LibPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  s.netHttpWf

instance mathRand_isPkgInit_inst [s : LibPkgState GF] : IsPkgInit (IProp GF) pkg_id.math.rand :=
  s.mathRandInit
instance mathRand_get_isPkgInit_wf_inst [s : LibPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.math.rand :=
  s.mathRandWf

end defs

end gryff.hyp

end Perennial
