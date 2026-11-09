/-
## `(*tokenSimple).isValidSimpleToken(ctx, token)` (internal helper)

**Users.** `tokenSimple.info`.

**Proof sketch.** `strings.Split(token, ".")` (not two parts: `false`); `strconv.ParseUint` of the index (an error: `false`); `select` on `t.indexWaiter(index)` (the waiter, `simpleAt`'s `waiterOk`: `recvOk`) or `ctx.Done()` (`Context.Done.spec`, `doneRecv`): `true` once the index is applied, `false` once the context is done; it may block (a context never done, an index never applied).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

**Margin.** The answer is not stated (`info` relies on the map, not on it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal
public import Spec.context.Api

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

/-- **`t.isValidSimpleToken(ctx, tok)`**: some answer; no panic. -/
def tokenSimple.isValidSimpleToken.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (ctx : GoInterface) (tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ ∗ Context.ctxOk ctx }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"isValidSimpleToken")) (Val #ctx)) (Val #tok))
  {{ (b : Bool), RET #b; True }}

end spec
end Auth
end EtcdGrove
end Perennial
