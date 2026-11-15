/-
## `(*tokenSimple).assign(ctx, username, rev)` (internal helper)

**Users.** `tp_assign` (the bundle), through `authStore.Authenticate` (an `Authenticate` context).

**Proof sketch.** `ctx.Value(AuthenticateParamIndex{})` as a `uint64` (`authnCtx`: `idx`), the prefix (`authnCtx`: present, a `string`: the unchecked assertion, `nonissues/etcd-auth-simple-token-assign-prefix-panic.md`, cannot fail), `fmt.Sprintf("%s.%d")` (`simpleTok p idx`), `assignSimpleTokenToUser` (its spec, with `simpleFresh` from `simpleFrom_fresh` and `tokenUser` from `authnCtx`; verify round: was the internal opaque `simpleAuthn`). A context without the index (`errors.New("failed to assign")`) is not covered: no caller passes one but `WithRoot`, at index `0`, which needs `rootTokOk` (not given by this provider).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

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

/-- **`t.assign(ctx, name, rev)`** from an `Authenticate` context at a fresh index: a token the
cluster issued to `name`. -/
def tokenSimple.assign.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (R : IProp GF) (ctx : GoInterface) (name : GoString) (rev : w64) (n idx : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ R ∗ Context.ctxOk ctx ∗ authnCtx γ ctx name idx ∗ simpleFrom t n ∗
      ⌜n < idx⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"assign")) (Val #ctx)) (Val #name)) (Val #rev))
  {{ (tok : GoString) (err : GoInterface), RET (PairV #tok #err); simpleFrom t idx ∗
      ⌜err = GoInterface.nil⌝ ∗ tokenUser γ tok name }}

end spec
end Auth
end EtcdGrove
end Perennial
