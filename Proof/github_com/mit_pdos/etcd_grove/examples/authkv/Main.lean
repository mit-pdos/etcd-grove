/-
`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b): **not proved** (a `sorry`). Lean-first
(no Rocq counterpart).

What the proof needs (`notes/decisions.md`, "E2b", "E2e" and "E2f of the auth plan"):
- **the server in the mode `on γa`** (E2e's next step, E2g): `NewServer.spec` generic in the auth
  mode, the store from `auth.newAuthStore_boot` (D22's part the named premise
  `auth.authSchemaBoot`, the provider's `auth.tokenProviderBoot`), `srvAuthBound` from
  `srvAuthBound_of_authInv`, the apply thread admitting auth requests with the authority
  `authOwn`;
- **`SetUp`'s admin calls**: the client's `Auth` field (not in `isNewClient`'s model; `NewAuth`,
  `RetryAuthClient` and the `authClient` methods untranslated) and the server's Auth service as
  `isGrpcRpc` contracts over the apply layer's admin steps (`apply.isAuthSteps`); the history
  after them `setupSt` at every later position (`auth.authHistHalf_lookup`, S4f);
- **the client's auth contract** over the contexts' metadata (`ClientAuth.lean`): C1
  (`userAttemptOk`) and C2/C4 (`deliversOutgoing`) in the client's attempt contract
  (`grpcInvokerOk` says nothing of metadata today), C3 the spec
  `metadata.AppendToOutgoingContext.spec` (a trust-boundary axiom; `reqCtx` proved over it), and
  that `reqCtx`'s timeout context has no outgoing token (Perennial's context model does not
  describe values at other keys); the bad principal is then unbound (`badCtx_unbound`);
- **the workload** (`Work`): each call's reply at the server's verdict -- an error for a refused
  principal (A1, A4), the persistent-update case of the client's write results for the bad
  principal's resent writes (E2d) -- and the checks, proved (`refused`, `checkKVs`,
  `checkTxnReads`, `CheckHistory`, `Writer`, `LastIn`, `keyOf`: E2f).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Work
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.CheckHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.LastIn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Main.wp_proof
    (wp_SetUp : SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_Work : Work.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_CheckHistory : CheckHistory.spec (GF := GF) (hG := hG))
    (wp_LastIn : LastIn.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authkv
end EtcdGrove
end Perennial
