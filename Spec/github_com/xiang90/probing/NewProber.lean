/-
## `probing.NewProber(rt)`: assumed

**Users.** `Transport.Start` (`rafthttp/transport.go:146-147`). Snippet: `probing.go`
(`ReqProberLifecycle`). **Assumed** (`prober.go`): a struct with a map of targets and the round
tripper (`http.DefaultTransport` if nil). **Changes.** From `specs-ref`'s `NewProber.lean`, with
`AddHTTP` in the bundle (rafthttp's `addPeerToProber`). **Margin.** None.
-/
module

public import Spec.github_com.xiang90.probing.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Probing

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.xiang90.probing.Assumptions]

/-- **A prober.** -/
def NewProber.spec : Prop :=
  ∀ (rt : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.probing }}
    (App (Val (@! github_com.xiang90.probing.NewProber)) (Val #rt))
  {{ (p : GoInterface), RET #p; proberOk p }}

end spec
end Probing
end EtcdGrove
end Perennial
