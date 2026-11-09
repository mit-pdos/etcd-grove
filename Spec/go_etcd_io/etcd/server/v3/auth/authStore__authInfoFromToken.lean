/-
## `(*authStore).authInfoFromToken(ctx, token)` (internal helper)

**Users.** `AuthInfoFromCtx`.

**Proof sketch.** The provider's `info(ctx, token, as.Revision())` (`tpOpen`, the opened `tokenProviderAt` contract).

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary. Verify round
(A9 3d F7): the provider's gate (`authGate γa R ∗ □ R`), which `info`'s waiter needs.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api
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

/-- **`as.authInfoFromToken(ctx, tok)`**: not valid, or an `AuthInfo` naming the user the cluster
issued `tok` to. -/
def authStore.authInfoFromToken.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (R : IProp GF) (ctx : GoInterface) (tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authGate γa R ∗ □ R ∗ Context.ctxOk ctx }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"authInfoFromToken")) (Val #ctx)) (Val #tok))
  {{ (ai : Loc) (ok : Bool), RET (PairV #ai #ok);
      ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ∃ (u : GoString) (rev : w64), tokenUser γ tok u ∗
        authInfoAt ai DFrac.discard u rev) }}

end spec
end Auth
end EtcdGrove
end Perennial
