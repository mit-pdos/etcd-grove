/-
# `client/v3/credentials` (batch 1c): the token bundle

* `tokFor γ who tok` (def): a token the bundle may hold for a client of principal `who`: `""`, or
  one naming `who`'s user (W0's `tokenUser`).
* `rpcCredsAt v γ who` (persistent): the `grpccredentials.PerRPCCredentials` value `v` (the bundle's
  `*perRPCCredential`) attaches, to each request, no token or a `tokFor` one (2a's dial reads it
  through `GetRequestMetadata`). Intended realization: an `RWMutex` whose invariant holds
  `authToken` with `tokFor`.
* `tokenMd m tok` (persistent; slot 2a): the `map[string]string` `m` is `{"token": tok}`.
* `credMD γ who mdc` (def; integration X, was 2a's slot `V3rpc.credMD`): the metadata the
  credentials add to a request: none, or `token: tok` with a non-empty `tokFor` token. What the
  dial passes as grpc's `R` (`rpcCredsAt_perRPC`: grpc's `perRPCAt`), and what 2a's `mdPrin_of` reads.

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
opaque rpcCredsAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **`m` is the metadata `{"token": tok}`** (persistent; slot 2a). -/
opaque tokenMd [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (tok : GoString) : IProp GF := iprop(True)

/-- **The metadata the credentials add to a request** (integration X; 2a's `mdPrin_of` takes it): none
(an empty token: `GetRequestMetadata` returns `nil`), or the key `token` with a non-empty token the
bundle may hold. -/
def credMD (γ : Cluster) (who : Principal) (mdc : Grpc.MD) : IProp GF :=
  iprop(⌜mdc = []⌝ ∨ ∃ tok, ⌜tok ≠ [] ∧ mdc = [(go!"token", [tok])]⌝ ∗ tokFor γ who tok)

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

/-- **The credentials are grpc's per-RPC credentials adding `credMD`** (what the dial's
`grpc.WithPerRPCCredentials` hands grpc: `GetRequestMetadata`'s spec, the map's keys already
lowercase). -/
def rpcCredsAt_perRPC.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  rpcCredsAt (GF := GF) v γ who ⊢ Grpc.perRPCAt v (credMD γ who)

end res

end Credentials
end EtcdGrove
end Perennial
