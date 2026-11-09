/-
## `(*tokenSimple).disable()` (internal helper)

**Users.** `tp_disable`, through `AuthDisable`, `Close`.

**Proof sketch.** `simpleTokensMu.Lock()`; the keeper taken (with its stop right) and set `nil`, the map replaced by an empty one (every token dropped); `Unlock`; a keeper: `stop()` (its spec: the goroutine done, its `threadTok` back into the invariant).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`t.disable()`**: no panic, nothing a caller observes. -/
def tokenSimple.disable.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ R }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"disable")) (Val #()))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
