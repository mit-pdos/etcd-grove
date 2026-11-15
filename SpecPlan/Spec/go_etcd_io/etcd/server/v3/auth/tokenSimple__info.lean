/-
## `(*tokenSimple).info(ctx, token, revision)` (internal helper)

**Users.** `tp_info` (the bundle), through `authStore.authInfoFromToken`.

**Proof sketch.** `isValidSimpleToken(ctx, token)` (its spec; `false`: `nil, false`); `simpleTokensMu.Lock()`; the map's user (`simpleAt`'s invariant: `tokenUser γ token u`); present with a keeper: `resetSimpleToken` (its spec, under the lock); `Unlock`; `&AuthInfo{username, revision}` and the presence (absent: `ok = false`, the `AuthInfo` names `""`).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`). Verify round (A9 3d F7): the waiter's gate `□ R` (`simpleAt t γ R`), which the index
waiter needs.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Internal
public import SpecPlan.Spec.context.Api

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

/-- **`t.info(ctx, tok, rev)`**: refused, or an `AuthInfo` naming the user the cluster issued `tok`
to, at `rev`. -/
def tokenSimple.info.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (R : IProp GF) (ctx : GoInterface) (tok : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ R ∗ □ R ∗ Context.ctxOk ctx }}
    (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"info")) (Val #ctx)) (Val #tok)) (Val #rev))
  {{ (ai : Loc) (ok : Bool), RET (PairV #ai #ok);
      ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ∃ u : GoString, tokenUser γ tok u ∗ authInfoAt ai DFrac.discard u rev) }}

end spec
end Auth
end EtcdGrove
end Perennial
