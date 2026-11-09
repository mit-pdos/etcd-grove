/-
## `(*tokenSimple).assignSimpleTokenToUser(username, token)` (internal helper)

**Users.** `tokenSimple.assign`.

**Proof sketch.** `simpleTokensMu.Lock()`; no keeper (disabled): nothing stored; the token in the map: `lg.Panic`, ruled out by `simpleFresh`; else `simpleTokens[token] = username` (the invariant gains it, with `tokenUser`) and the keeper's `addSimpleToken` (its spec); `Unlock`.

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

**Margin.** `WithRoot`'s index-`0` tokens have no `simpleFresh` (`nonissues/etcd-auth-withroot-token-collision-panic.md`).
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

/-- **`t.assignSimpleTokenToUser(name, tok)`** of a fresh token the cluster issued to `name`. -/
def tokenSimple.assignSimpleTokenToUser.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (name tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ ∗ simpleFresh t tok ∗ tokenUser γ tok name }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"assignSimpleTokenToUser")) (Val #name)) (Val #tok))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
