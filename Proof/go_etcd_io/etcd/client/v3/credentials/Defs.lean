/-
**The client's token bundle** (`client/v3/credentials`, the auth plan's E2d, 2026-10-25): what
`clientv3.New` makes for a client with a user name and password (`NewPerRPCCredentialBundle`), and
what its dial reads of it (`PerRPCCredentials`, passed to grpc's `WithPerRPCCredentials`).
Lean-first (no Rocq counterpart).

`tokenBundleInv atb P` (persistent; the auth plan's C1, 2026-10-28, `notes/c1-plan.md`): `atb` is a
`*perRPCCredentialBundle` whose `rc` field (its `*perRPCCredential`) is read-only, with
`credTokInv rc P`, the guard of `rc.authTokenMu` over `rc`'s `authToken` field: `""` or a token
meeting `□ P` (and the bound `threadBound GF ≤ 2^30` on its readers). `rc`'s `UpdateAuthToken`
(given `""` or a `P`-token) is proved over its body (a writer needs only the guard; 2026-11-22);
`GetRequestMetadata` (metadata meeting `tokMdOk P`: none, or the one key `token` with a `P`-token)
is a trust-boundary axiom over it (its `RWMutex` read lock needs a reader token, or a thread token
to borrow one from the pool, which grpc's per-attempt call cannot give: `notes/c1-plan.md`,
finding 2).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.credentials
public import Proof.google_golang_org.grpc.InvGrpc
public import Perennial.Proof.sync.RWMutexThreads

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

/-- **The per-RPC credentials' metadata of a bundle whose tokens meet `P`** (persistent if `P`
is; the auth plan's C1): none, or only the key `token` (`rpctypes.TokenFieldNameGRPC`), with one
token meeting `□ P`. -/
def tokMdOk (P : GoString → IProp GF) (cm : GrpcMd) : IProp GF :=
  iprop(⌜∀ k, k ≠ go!"token" → mdGet cm k = none⌝ ∗
    (⌜mdGet cm go!"token" = none⌝ ∨ ∃ t, ⌜mdGet cm go!"token" = some [t]⌝ ∗ □ P t))

instance tokMdOk_persistent (P : GoString → IProp GF) (cm : GrpcMd) :
    Persistent (tokMdOk P cm) := by
  unfold tokMdOk; infer_instance

/-- The credentials' invariant's namespace. -/
def credTokN : Namespace := nroot.@"etcd_client_creds"

/-- **What `rc.authTokenMu` guards, at fraction `q`**: the `authToken` field, `""` or a token
meeting `□ P` (prove-ps2-client, 2026-11-22). -/
def credTokR (rc : Loc) (P : GoString → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ t : GoString,
    structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authToken" rc
      ↦{DFrac.own q} t ∗ (⌜t = go!""⌝ ∨ □ P t))

instance credTokR_fractional (rc : Loc) (P : GoString → IProp GF) :
    Fractional (credTokR (GF := GF) rc P) where
  fractional q1 q2 := by
    have hpt : ∀ v : GoString,
        (structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authToken" rc
          ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authToken" rc
          ↦{DFrac.own q1} v ∗
        structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authToken" rc
          ↦{DFrac.own q2} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1) (DFrac.own q2)
    refine ⟨?_, ?_⟩
    · iintro H
      unfold credTokR
      icases H with ⟨%t, Ht, #Hp⟩
      icases (hpt t).1 $$ Ht with ⟨Ht1, Ht2⟩
      isplitl [Ht1]
      · iexists t; iframe Ht1 Hp
      · iexists t; iframe Ht2 Hp
    · iintro ⟨H1, H2⟩
      unfold credTokR
      icases H1 with ⟨%t, Ht1, #Hp⟩
      icases H2 with ⟨%t2, Ht2, -⟩
      icombine Ht1 Ht2 gives %He
      subst He
      iexists t
      iframe Hp
      iapply (hpt t).2; iframe

/-- **The token of the per-RPC credentials `rc` is `""` or meets `P`** (persistent; the auth
plan's C1, see the file header): `rc.authTokenMu`'s guard over `credTokR` (what a writer needs,
`RWMutex.wp_Lock_guard`), its reader tokens in a thread pool, `sync`'s initialization, and the
bound on the goroutines its readers are (`RWMutex`'s 2^30 concurrent readers; C1's review, Q6),
which the trust-boundary `GetRequestMetadata` rests on. Until 2026-11-22 a bare invariant over
the field (prove-ps2-client: the lock, so that `UpdateAuthToken` is proved over its body). -/
def credTokInv (rc : Loc) (P : GoString → IProp GF) : IProp GF :=
  iprop(⌜threadBound GF ≤ 2 ^ 30⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isRWMutexGuard
      (structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authTokenMu" rc)
      (credTokR rc P) ∗
    ∃ γp : GName, threadPool.isThreadPool credTokN γp (sync.ownRWMutex
      (structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authTokenMu" rc)
      (credTokR rc P)))

instance credTokInv_persistent (rc : Loc) (P : GoString → IProp GF) :
    Persistent (credTokInv rc P) := by
  unfold credTokInv; infer_instance

/-- **The token bundle `atb`, its tokens `""` or meeting `P`** (persistent; the auth plan's C1). -/
def tokenBundleInv (atb : GoInterface) (P : GoString → IProp GF) : IProp GF :=
  iprop(∃ b rc : Loc,
    ⌜atb = interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty) #b⌝ ∗
    structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle go!"rc" b ↦□ rc ∗
    credTokInv rc P)

instance tokenBundleInv_persistent (atb : GoInterface) (P : GoString → IProp GF) :
    Persistent (tokenBundleInv atb P) := by
  unfold tokenBundleInv; infer_instance

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
