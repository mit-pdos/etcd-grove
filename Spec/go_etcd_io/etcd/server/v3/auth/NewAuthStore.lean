/-
## `NewAuthStore(lg, be, tp, bcryptCost)`

**Users.** `NewServer` (`server.go:369`, 2e), with `schema.NewAuthBackend(lg, be)` over the member's
backend and `NewTokenProvider`'s provider. Snippet: `examples/specreq/auth/boot.go` (`ReqBoot`).

**Proof sketch.** A nil logger: `zap.NewNop()`; the cost normalized; `CreateAuthBuckets`, the batch
transaction (4b: `authBackendAt be a`), the flag and revision read; the store allocated; on: the
provider's `enable()`; revision `0` (a fresh backend): `commitRevision` (`normRev`);
`setupMetricsReporter`; `refreshRangePermCache`; `Unlock`, `ForceCommit`. The batch lock
(4b's `authBatchTx.Lock`, `LockInsideApply`) runs the backend's post-lock hook, which the server sets
only after this call (`server.go:369` then `409`): `authBackendAt be a` as given here must say the
hook is not set yet (4a's `beHook … func.nil`: `hookRun` is then the caller's view shift, with
`Pre = Q = True`); after `Recover` the hook is the server's (`authHook`, the writer's per call).
Integration I5: 2e's `NewServer` must hand over the backend before setting its hook. The history allocated with
`normRev a` at index `0` (`authReached`, `validPerms`), the invariants, the provider's contract
opened, `tokFrom γa 0` (a fresh simple provider has assigned nothing), `rootTokOk` if the provider
gives it.

**Changes.** The old spec (`authStoreKit`, per mode, an axiom with auth off; the backend's buckets,
the reader stock `List.replicate actualMaxReaders RD`) restated over 4b's `authBackendAt`, W0's
state, and the thread tokens of the readers (no reader stock: bounds plan). `tp ≠ nil`
(`nonissues/etcd-auth-newauthstore-nil-tp.md`) is in `tokenProviderAt`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api
public import Spec.go_uber_org.zap.Api

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

/-- **`NewAuthStore(lg, be, tp, cost)`**: a store over the backend's auth state (its revision `1`
if fresh), which the cluster reached, as the store's state `0`, held by the caller (the writer). -/
def NewAuthStore.spec : Prop :=
  ∀ (lg : Loc) (be tp : GoInterface) (cost : w64) (γ : Cluster) (a : AuthState) (rt : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ authBackendAt be a ∗ tokenProviderAt tp γ rt ∗
      authReached γ (normRev a) ∗ ⌜validPerms a ∧ recordsFit (normRev a)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg)) (Val #be))
      (Val #tp)) (Val #cost))
  {{ (s : GoInterface), RET #s; ∃ (st : Loc) (γa : AuthNames),
      ⌜s = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty) #st⌝ ∗
      authStoreAt st γ γa ∗ authCur γa 0 (normRev a) ∗ tokFrom γa 0 ∗
      (if rt then rootTokOk γa else True) }}

end spec
end Auth
end EtcdGrove
end Perennial
