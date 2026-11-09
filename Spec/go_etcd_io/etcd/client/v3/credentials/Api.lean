/-
# `client/v3/credentials` (batch 1c): the token bundle

* `tokFor γ who tok` (def): a token the bundle may hold for a client of principal `who`: `""`, or
  one naming `who`'s user (W0's `tokenUser`).
* `rpcCredsAt v γ who` (persistent): the `grpccredentials.PerRPCCredentials` value `v` (the bundle's
  `*perRPCCredential`) attaches, to each request, no token or a `tokFor` one (2a's dial reads it
  through `GetRequestMetadata`). Intended realization: an `RWMutex` whose invariant holds
  `authToken` with `tokFor`.
* `tokenMd m tok` (persistent; slot 2a): the `map[string]string` `m` is `{"token": tok}`.

`ClientV3.bundleAt b γ who` (the bundle interface value) is realized from `rpcCredsAt` of its `rc`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient
public import GeneratedProof.go_etcd_io.etcd.client.v3.credentials
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.credentials

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Credentials

open Iris Iris.BI

open EtcdModel ClientV3

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A token a client of principal `who` may send. -/
def tokFor (γ : Cluster) (who : Principal) (tok : GoString) : IProp GF :=
  iprop(⌜tok = []⌝ ∨ ∃ u, ⌜who = some u⌝ ∗ tokenUser γ tok u)

/-- **Per-RPC credentials attaching `who`'s tokens** (persistent). -/
opaque rpcCredsAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **`m` is the metadata `{"token": tok}`** (persistent; slot 2a). -/
opaque tokenMd (m : Loc) (tok : GoString) : IProp GF := iprop(True)

def rpcCredsAt_persistent.spec : Prop := ∀ v γ who, Persistent (rpcCredsAt (GF := GF) v γ who)

/-- The bundle's credentials. -/
def bundleAt_unfold.spec : Prop := ∀ (b : Loc) (γ : Cluster) (who : Principal),
  bundleAt (GF := GF)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty) #b)
    γ who ⊣⊢
  ∃ rc : Loc,
    b ↦□ ({ rc' := rc } : go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle) ∗
    rpcCredsAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty) #rc)
      γ who

end res

end Credentials
end EtcdGrove
end Perennial
