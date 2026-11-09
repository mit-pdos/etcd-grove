/-
## `probing.NewHandler()`: assumed

**Users.** `Transport.Handler` (`rafthttp/transport.go:166`: at `ProbingPrefix`, `/raft/probing`).
Snippet: `examples/specreq/pkgleaves/leaves.go` (`ReqProberLifecycle`).

**Assumed** (`server.go`): `&httpHealth{}`, whose `ServeHTTP` encodes `Health{OK: true, Now:
time.Now()}` as JSON into the writer (a `Write`, committing `200` with no header set by it): so it
serves any protocol that allows, at every request under the pattern, a `200` with no headers and
any body. It reads nothing of the request.

**Changes.** From `specs-ref`'s `NewHandler.lean` (`handlerFor` over the old network): over 2f's
`Http.handlerOk`.

**Margin.** None.
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

/-- **A handler answering `200`** under any pattern whose protocol allows it. -/
def NewHandler.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.probing }}
    (App (Val (@! github_com.xiang90.probing.NewHandler)) (Val #()))
  {{ (h : GoInterface), RET #h;
      □ ∀ (P : Http.Proto GF) (pfx : GoString),
        (□ ∀ (R : Http.HReq) (τ : GName) (w : List w8), ⌜Http.pathUnder pfx R.path⌝ →
          P.resp R τ (W64 200) [] w) -∗
        Http.handlerOk h P pfx }}

end spec
end Probing
end EtcdGrove
end Perennial
