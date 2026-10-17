/-
**The client's token update** (`client/v3/client.go`'s `Client.UpdateAuthToken`, PR etcd#21909): the
vocabulary of its proof. Lean-first (no Rocq counterpart).

**The bundle** (`tokenBundleOk atb`, a contract): the client's `authTokenBundle` is not nil and its
`UpdateAuthToken(token)` returns. (The real bundle, `credentials.perRPCCredentialBundle`, takes its
credential's `RWMutex` to store the token: safe to call concurrently; `client/v3/credentials` is
translated names only.)

**What it shows** (`retryClientOk_excl_token`): `UpdateAuthToken` writes the field `Client.Token`,
so its spec needs that field owned (`Token ↦ _`). The verified retry interceptor reads the same
field on every failed call (`shouldRefreshToken`) and holds it read-only (`retryClientOk`, `↦□`,
`InvRetry.lean`): no client the interceptor runs on can also satisfy `UpdateAuthToken`'s
precondition. In Go terms: `c.Token` is a plain field written without synchronization while
request goroutines read it, a data race, contrary to the method's doc comment ("safe to call
concurrently with other operations").
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The token bundle** `atb` (a `credentials.PerRPCCredentialsBundle`, a contract): not nil, its
`UpdateAuthToken(token)` returns. -/
def tokenBundleOk (atb : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜atb = GoInterface.ok ti⌝ ∗
    □ (∀ (token : GoString),
      {{ True }}
        (App (Val #(methods ti.ty go!"UpdateAuthToken" ti.v)) (Val #token))
      {{ RET #(); True }}))

instance tokenBundleOk_persistent (atb : GoInterface) :
    Persistent (tokenBundleOk (GF := GF) atb) := by
  unfold tokenBundleOk; infer_instance

/-- **`UpdateAuthToken`'s precondition excludes the retry interceptor's client**: the field
`Token` owned and held read-only at once is impossible. -/
theorem retryClientOk_excl_token (c : Loc) (tok : GoString) :
    retryClientOk (GF := GF) c ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c ↦ tok ⊢ False := by
  iintro ⟨Hc, Ht⟩
  iunfold retryClientOk at Hc
  icases Hc with ⟨-, -, %tok', %atb, Hro, -, -⟩
  icombine Hro Ht gives %Heq
  subst Heq
  ihave Hro' := typedPointsto_split _ _ _ $$ Hro
  ihave Ht' := typedPointsto_split _ _ _ $$ Ht
  ihave H := ((typedPointstoDef_dfractional (GF := GF)
    (structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c) tok').dfractional
      DFrac.discard (DFrac.own 1)).2 $$ [Hro' Ht']
  · isplitl [Hro']
    · iexact Hro'
    · iexact Ht'
  ihave %Hval : ⌜✓ (DFrac.discard • DFrac.own 1)⌝ $$ [H]
  · iapply (heapPointsto_valid (structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c)
      (DFrac.discard • DFrac.own 1) #tok')
    iapply (show typedPointstoDef (GF := GF)
        (structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c) tok'
        (DFrac.discard • DFrac.own 1) ⊢
      heapPointsto (structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c)
        (DFrac.discard • DFrac.own 1) #tok' from .rfl)
    iexact H
  have h := DFrac.valid_op_own Hval
  exact absurd h (by simp)

end defs

end EtcdGrove
end Perennial
