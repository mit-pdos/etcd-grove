/-
**The client's token bundle** (`client/v3/credentials`, the auth plan's E2d, 2026-10-25): what
`clientv3.New` makes for a client with a user name and password (`NewPerRPCCredentialBundle`), and
what its dial reads of it (`PerRPCCredentials`, passed to grpc's `WithPerRPCCredentials`).
Lean-first (no Rocq counterpart).

`tokenBundleAt atb` (persistent): `atb` is a `*perRPCCredentialBundle` whose `rc` field (its
`*perRPCCredential`) is read-only. Nothing is said of the token behind it (`rc`'s `authToken` under
its lock): the client's `getToken` writes it (an axiom, `Client__getToken.lean`) and grpc reads it
for each attempt (`GetRequestMetadata`), neither modelled; which token an attempt carries is the
client's auth contract (`notes/decisions.md`, "E2b of the auth plan", C1).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.credentials

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The token bundle `atb`** (persistent; see the file header). -/
def tokenBundleAt (atb : GoInterface) : IProp GF :=
  iprop(∃ b rc : Loc,
    ⌜atb = interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty) #b⌝ ∗
    structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle go!"rc" b ↦□ rc)

instance tokenBundleAt_persistent (atb : GoInterface) :
    Persistent (tokenBundleAt (GF := GF) atb) := by
  unfold tokenBundleAt; infer_instance

end defs

section types
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- The bundle's struct type, from its `TypeAssumptions` (as `InvCmpTypes.lean`'s). -/
instance (priority := high) credentials_bundle_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.underlying
      go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.underlying)

instance (priority := high) credentials_cred_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.credentials.perRPCCredential.underlying
      go_etcd_io.etcd.client.v3.credentials.perRPCCredential :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.credentials.perRPCCredential.underlying)

end types

end EtcdGrove
end Perennial
